-- Prove2me | solution 1 for SemAC02.Supplement.theorem_7_12_quasipoly_spsp
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T10:34:49.256216+00:00
-- url     : https://prove2.me/submissions/22110957-b34a-47cb-bf13-849a43e8fb3e

import Definitions.Def_SemAC02_Supplement_selLift
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_SemAC02_Supplement_randCNF
import Mathlib
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Theorems.Thm_SemAC02_Supplement_theorem_7_9_lifting_bounded_bottom
import Theorems.Thm_SemAC02_Supplement_theorem_7_2_random_log_width

open _root_.SemAC02 _root_.SemAC02.Supplement
open _root_.AC02Frege
namespace P2MRandomSelectorLiftProof
section
-- Inlined Solutions.P2MSelectorLiftCounts

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSelectorLiftCounts

open LiftSAParity

noncomputable def pairs (q : ℕ) : Finset (Finset (Bool×Fin q)) :=
  Finset.univ.filter (fun S => S.card=2)

theorem pairs_card (q : ℕ) : (pairs q).card ≤ (2*q)^2 := by
  have he : pairs q=(Finset.univ : Finset (Bool×Fin q)).powersetCard 2 := by
    ext S; simp [pairs]
  rw [he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  exact Nat.choose_le_pow _ _

theorem sum_bound {I : Type} (L : List I) (f : I → ℕ) (B : ℕ) (hf : ∀ i∈L, f i ≤ B) :
    (L.map f).sum ≤ L.length*B := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have hh := ih (fun j hj => hf j (by simp [hj]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    have hi := hf i (by simp)
    nlinarith

theorem length_bound {n q : ℕ} (F : List (Clause (Fin n))) :
    (selLift q F).length ≤ n+n*(2*q)^2+F.length := by
  have he : (selLift q F).length=n+n*(pairs q).card+F.length := by
    simp [selLift,pairs,List.length_flatMap,Nat.add_assoc]
  rw [he]
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left n (pairs_card q)) n) _

theorem lifted_clause_card {n q : ℕ} (C : Clause (Fin n)) :
    (C.biUnion (fun l => Finset.univ.image (fun a : Fin q => ((l.1,l.2,a),true)))).card ≤ q*C.card := by
  calc
    _ ≤ ∑ l∈C, (Finset.univ.image (fun a : Fin q => ((l.1,l.2,a),true))).card := Finset.card_biUnion_le
    _ ≤ ∑ _l∈C, q := Finset.sum_le_sum (fun l hl => by simpa using Finset.card_image_le (s:=Finset.univ) (f:=fun a : Fin q => ((l.1,l.2,a),true)))
    _ = _ := by simp [Nat.mul_comm]

theorem literals_bound {n q : ℕ} (F : List (Clause (Fin n))) :
    ((selLift q F).map Finset.card).sum ≤
      n*(2*q)+n*(2*(2*q)^2)+q*((F.map Finset.card).sum) := by
  classical
  let A := (List.finRange n).map (fun i => Finset.univ.image (fun c : Bool×Fin q => ((i,c),true)))
  let B := (List.finRange n).flatMap (fun i => (pairs q).toList.map (fun S => S.image (fun c => ((i,c),false))))
  let D := F.map (fun C => C.biUnion (fun l => Finset.univ.image (fun a : Fin q => ((l.1,l.2,a),true))))
  have hA : (A.map Finset.card).sum ≤ n*(2*q) := by
    dsimp [A]
    rw [List.map_map]
    apply (sum_bound (List.finRange n) _ (2*q) _).trans_eq (by simp)
    intro i hi
    simpa using Finset.card_image_le (s:=Finset.univ) (f:=fun c : Bool×Fin q => ((i,c),true))
  have hBlock (i : Fin n) :
      (((pairs q).toList.map (fun S => S.image (fun c => ((i,c),false)))).map Finset.card).sum ≤ 2*(pairs q).card := by
    rw [List.map_map]
    have hh := sum_bound (pairs q).toList (fun S => (S.image (fun c => ((i,c),false))).card) 2 (by
      intro S hS
      have hcard := (Finset.mem_filter.mp (Finset.mem_toList.mp hS)).2
      exact Finset.card_image_le.trans_eq hcard)
    simpa only [Finset.length_toList,Nat.mul_comm,Function.comp_def] using hh
  have hB : (B.map Finset.card).sum ≤ n*(2*(2*q)^2) := by
    dsimp [B]
    rw [List.map_flatMap,List.flatMap_def,List.sum_flatten,List.map_map]
    have hh := sum_bound (List.finRange n) _ (2*(pairs q).card) (fun i hi => hBlock i)
    have hc : n*(2*(pairs q).card) ≤ n*(2*(2*q)^2) := Nat.mul_le_mul_left n (Nat.mul_le_mul_left 2 (pairs_card q))
    have hh' : (List.map (fun i : Fin n =>
        (List.map Finset.card ((pairs q).toList.map (fun S => S.image (fun c => ((i,c),false))))).sum) (List.finRange n)).sum ≤
        n*(2*(pairs q).card) := by simpa only [List.length_finRange] using hh
    exact hh'.trans hc
  have hD : (D.map Finset.card).sum ≤ q*((F.map Finset.card).sum) := by
    dsimp [D]
    rw [List.map_map]
    induction F with
    | nil => simp
    | cons C F ih =>
      simp only [List.map_cons,List.sum_cons,Nat.mul_add]
      exact Nat.add_le_add (lifted_clause_card C) ih
  have he : selLift q F=A++B++D := rfl
  rw [he,List.map_append,List.map_append,List.sum_append,List.sum_append]
  exact Nat.add_le_add (Nat.add_le_add hA hB) hD

end SemAC02.Supplement.P2MSelectorLiftCounts
end

section
-- Inlined Solutions.P2MLogGrowth

open Filter Topology

namespace ProofComplexity.P2MLogGrowth

theorem eventually_log_large (b : ℝ) : ∀ᶠ n : ℕ in atTop, b ≤ Real.log (n : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop b

theorem eventually_log_power_le (A : ℝ) (k : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, A*(Real.log (n : ℝ))^k ≤ (n : ℝ)^C := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hC).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hb := (h.const_mul_left A).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb] with n hn
  have he : |A*(Real.log (n : ℝ))^k| ≤ (n : ℝ)^C := by
    simpa only [Function.comp_apply,Real.rpow_natCast,Real.norm_eq_abs,one_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) C)] using hn
  exact (le_abs_self _).trans he

theorem eventually_scaled_power_le (A p q : ℝ) (hpq : p < q) :
    ∀ᶠ n : ℕ in atTop, A*(n : ℝ)^p ≤ (n : ℝ)^q := by
  have hlarge := ((tendsto_rpow_atTop (by linarith : 0 < q-p)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_ge_atTop A
  filter_upwards [hlarge,eventually_ge_atTop 1] with n hn hn1
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ (n : ℝ)^(q-p)*(n : ℝ)^p := mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hnp.le _)
    _ = (n : ℝ)^((q-p)+p) := (Real.rpow_add hnp _ _).symm
    _ = _ := by congr 1; ring

end ProofComplexity.P2MLogGrowth
end

section
-- Inlined Solutions.P2MCeilingLogEstimates

set_option maxHeartbeats 1000000

namespace ProofComplexity.P2MCeilingLogEstimates

open Filter

theorem power_upper (n : ℕ) (hn : 1 ≤ n) : 2^Nat.clog 2 n ≤ 2*n := by
  generalize he : Nat.clog 2 n=l
  cases l with
  | zero => simpa using (show 1 ≤ 2*n by omega)
  | succ l =>
    have hp : 2^l<n := (Nat.lt_clog_iff_pow_lt (by decide)).mp (by rw [he]; omega)
    simpa only [pow_succ,Nat.mul_comm] using Nat.mul_le_mul_left 2 hp.le

theorem lower (n : ℕ) : Real.logb 2 n ≤ (Nat.clog 2 n : ℝ) := by
  rw [←Real.natCeil_logb_natCast 2 n]
  exact Nat.le_ceil _

theorem upper (n : ℕ) (hn : 1 ≤ n) : (Nat.clog 2 n : ℝ) ≤ Real.log n/Real.log 2+1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1 : ℝ)<2) hnR)
  have he : ⌈Real.logb (2 : ℝ) (n : ℝ)⌉₊=Nat.clog 2 n := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 n
  rw [he] at hh
  exact hh.le

theorem eventually_scaled_le (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop, A*(Nat.clog 2 n : ℝ) ≤ n := by
  have hlog := P2MLogGrowth.eventually_log_power_le (2*A/Real.log 2) 1 (C:=1) (by norm_num)
  have hlarge := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop (2*A)
  filter_upwards [hlog,hlarge,eventually_ge_atTop 1] with n hn hAn hn1
  simp only [pow_one,Real.rpow_one] at hn
  have hu := mul_le_mul_of_nonneg_left (upper n hn1) hA
  simp only [div_eq_mul_inv] at hn hu
  nlinarith

end ProofComplexity.P2MCeilingLogEstimates
end

section
-- Inlined Solutions.P2MRandomSelectorLiftCounts

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomSelectorLiftCounts

open LiftSAParity

theorem variable_count (n : ℕ) : Fintype.card (Fin n×Bool×Fin n)=2*n^2 := by simp [Nat.pow_two]; ring

theorem bounds (n : ℕ) (hn : 2 ≤ n)
    (ω : Fin (n*2^Nat.clog 2 n) → WClause n (Nat.clog 2 n)) :
    ((selLift n (List.ofFn (fun j => (ω j).1))).length : ℝ) ≤ (16/Real.log 2)*(n : ℝ)^3 ∧
    (((selLift n (List.ofFn (fun j => (ω j).1))).map Finset.card).sum : ℝ) ≤
      (16/Real.log 2)*(n : ℝ)^3*Real.log n := by
  let l := Nat.clog 2 n
  let F := List.ofFn (fun j => (ω j).1)
  have hlen : F.length=n*2^l := List.length_ofFn
  have hsum : (F.map Finset.card).sum=(n*2^l)*l := by
    simp [F,l,List.map_ofFn,List.sum_ofFn,(fun j => (ω j).2.1)]
  have hpow := ProofComplexity.P2MCeilingLogEstimates.power_upper n (by omega)
  have hm : ((n*2^l : ℕ) : ℝ) ≤ 2*(n : ℝ)^2 := by
    have hh : ((2^l : ℕ) : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast hpow
    push_cast at hh ⊢
    nlinarith
  have hL : ((selLift n F).length : ℝ) ≤ n+(n : ℝ)*(2*n)^2+((n*2^l : ℕ) : ℝ) := by
    have hh := P2MSelectorLiftCounts.length_bound (q:=n) F
    rw [hlen] at hh
    exact_mod_cast hh
  have hT : (((selLift n F).map Finset.card).sum : ℝ) ≤
      (n : ℝ)*(2*n)+(n : ℝ)*(2*(2*n)^2)+(n : ℝ)*(((n*2^l)*l : ℕ) : ℝ) := by
    have hh := P2MSelectorLiftCounts.literals_bound (q:=n) F
    rw [hsum] at hh
    exact_mod_cast hh
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn3 : (n : ℝ) ≤ (n : ℝ)^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg (n : ℝ))]
  have hn23 : (n : ℝ)^2 ≤ (n : ℝ)^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg (n : ℝ))]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2); linarith
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hl := ProofComplexity.P2MCeilingLogEstimates.upper n (by omega)
  constructor
  · have h7 : (7 : ℝ) ≤ 16/Real.log 2 := (le_div_iff₀ hl2).mpr (by nlinarith)
    apply le_trans _ (mul_le_mul_of_nonneg_right h7 (by positivity : (0 : ℝ) ≤ (n : ℝ)^3))
    nlinarith
  · have hbase : (2 : ℝ)*(n : ℝ)^2+8*(n : ℝ)^3 ≤ (10/Real.log 2)*(n : ℝ)^3*Real.log n := by
      apply le_trans (by nlinarith : (2 : ℝ)*(n : ℝ)^2+8*(n : ℝ)^3 ≤ 10*(n : ℝ)^3)
      have hh := mul_le_mul_of_nonneg_left hlogn (show 0 ≤ (10/Real.log 2)*(n : ℝ)^3 by positivity)
      have he : (10/Real.log 2)*(n : ℝ)^3*Real.log 2=10*(n : ℝ)^3 := by field_simp
      simpa only [he] using hh
    have hterm : (2 : ℝ)*(n : ℝ)^3*l ≤ (4/Real.log 2)*(n : ℝ)^3*Real.log n := by
      have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ (2 : ℝ)*(n : ℝ)^3 by positivity)
      have he : (2 : ℝ)*(n : ℝ)^3*(Real.log n/Real.log 2+1) ≤ (4/Real.log 2)*(n : ℝ)^3*Real.log n := by
        have hb : (1 : ℝ) ≤ Real.log n/Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hlogn)
        simp only [div_eq_mul_inv] at hb ⊢
        nlinarith [mul_nonneg (show 0 ≤ (n : ℝ)^3 by positivity) (sub_nonneg.mpr hb)]
      exact hh.trans he
    have hml := mul_le_mul_of_nonneg_left hm (show 0 ≤ (n : ℝ)*(l : ℝ) by positivity)
    change (((selLift n F).map Finset.card).sum : ℝ) ≤ _
    push_cast at hT hml ⊢
    simp only [div_eq_mul_inv] at hbase hterm ⊢
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ)^3 by positivity) (show 0 ≤ Real.log n by linarith)]

end SemAC02.Supplement.P2MRandomSelectorLiftCounts
end

section
-- Inlined Solutions.P2MSelectorLiftExponentComparison

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSelectorLiftExponentComparison

theorem base_dominates (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (n d : ℕ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hlog : 1 ≤ Real.log n)
    (hdlog : (d : ℝ) ≤ ε*Real.log n) (hC : ℝ) (hC0 : 0 < hC) (hCupper : hC ≤ Real.sqrt n)
    (hgrowth : (ε*(ε+3)/a)*(Real.log n)^3 ≤ Real.sqrt n) :
    (n : ℝ)^(d+1) ≤ 1/4*Real.exp (a*n/((d : ℝ)*hC)) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hdR : (0 : ℝ)<d := by exact_mod_cast (show 0 < d by omega)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hL : 0 ≤ 2+((d : ℝ)+1)*Real.log n := by positivity
  have hLupper : 2+((d : ℝ)+1)*Real.log n ≤ (ε+3)*(Real.log n)^2 := by
    have hh := mul_le_mul_of_nonneg_right hdlog (by linarith : 0 ≤ Real.log n)
    nlinarith [sq_nonneg (Real.log n-1)]
  have hD : (d : ℝ)*hC ≤ ε*Real.log n*Real.sqrt n :=
    mul_le_mul hdlog hCupper hC0.le (by positivity)
  have hprod : ((d : ℝ)*hC)*(2+((d : ℝ)+1)*Real.log n) ≤ a*n := by
    calc
      _ ≤ (ε*Real.log n*Real.sqrt n)*((ε+3)*(Real.log n)^2) :=
        mul_le_mul hD hLupper hL (by positivity)
      _ = a*((ε*(ε+3)/a)*(Real.log n)^3)*Real.sqrt n := by field_simp
      _ ≤ a*(Real.sqrt n)*(Real.sqrt n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrowth ha.le) hs.le
      _ = a*n := by rw [mul_assoc,←pow_two,Real.sq_sqrt hnR.le]
  have hexp : 2+((d : ℝ)+1)*Real.log n ≤ a*n/((d : ℝ)*hC) :=
    (le_div_iff₀ (mul_pos hdR hC0)).mpr (by nlinarith)
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have he := Real.add_one_le_exp (1 : ℝ)
    have he' : (Real.exp 1)^2=Real.exp 2 := by rw [←Real.exp_nat_mul]; congr 1; norm_num
    nlinarith
  have hpow : (n : ℝ)^(d+1)=Real.exp (((d : ℝ)+1)*Real.log n) := by
    simpa only [Nat.cast_add,Nat.cast_one,Real.exp_log hnR] using (Real.exp_nat_mul (Real.log (n : ℝ)) (d+1)).symm
  calc
    _ = Real.exp (((d : ℝ)+1)*Real.log n) := hpow
    _ ≤ 1/4*(Real.exp 2*Real.exp (((d : ℝ)+1)*Real.log n)) := by
      nlinarith [Real.exp_pos (((d : ℝ)+1)*Real.log n)]
    _ = 1/4*Real.exp (2+((d : ℝ)+1)*Real.log n) := by rw [Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)

end SemAC02.Supplement.P2MSelectorLiftExponentComparison
end

section
-- Inlined Solutions.P2MSelectorLiftAsymptoticParameters

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSelectorLiftAsymptoticParameters

open Filter

noncomputable def width (ε : ℝ) (n : ℕ) : ℕ := ⌊ε*Real.log n⌋₊

theorem eventually_valid (a C c : ℝ) (ha : 0 < a) (hC : 1 < C) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 1 ≤ width ε n ∧ (width ε n : ℝ) ≤ c*Real.logb 2 n ∧
      (n : ℝ)^(width ε n+1) ≤ 1/4*Real.exp (a*n/((width ε n : ℝ)*C^(width ε n))) ∧
      (n : ℝ)^((ε/2)*Real.log n) ≤ (n : ℝ)^(width ε n+1) := by
  have hln2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlnC : 0 < Real.log C := Real.log_pos hC
  let ε := min (c/(2*Real.log 2)) (1/(4*Real.log C))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεc : ε*(Real.log 2) ≤ c/2 := by
    have hh := (le_div_iff₀ (show 0 < 2*Real.log 2 by positivity)).mp (min_le_left (c/(2*Real.log 2)) (1/(4*Real.log C)))
    dsimp [ε]
    nlinarith
  have hεC : ε*Real.log C ≤ 1/4 := by
    have hh := (le_div_iff₀ (show 0 < 4*Real.log C by positivity)).mp (min_le_right (c/(2*Real.log 2)) (1/(4*Real.log C)))
    dsimp [ε]
    nlinarith
  refine ⟨ε,hε,?_⟩
  have hloglarge := ProofComplexity.P2MLogGrowth.eventually_log_large (max 1 (2/ε))
  have hgrowth := ProofComplexity.P2MLogGrowth.eventually_log_power_le (ε*(ε+3)/a) 3 (C:=1/2) (by norm_num)
  filter_upwards [hloglarge,hgrowth,eventually_ge_atTop 2] with n hloglarge hgrowth hn
  have hlog : 1 ≤ Real.log n := (le_max_left _ _).trans hloglarge
  have hlog0 : 0 ≤ Real.log n := by linarith
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hlarge : 2 ≤ ε*Real.log n := by
    have hh := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hloglarge) hε.le
    have he : ε*(2/ε)=2 := by field_simp
    rw [he] at hh
    exact hh
  have hd : 1 ≤ width ε n := Nat.le_floor (by norm_num; linarith)
  have hdU : (width ε n : ℝ) ≤ ε*Real.log n := Nat.floor_le (by positivity)
  have hdRange : (width ε n : ℝ) ≤ c*Real.logb 2 n := by
    rw [Real.logb, ←mul_div_assoc]
    have hh := mul_le_mul_of_nonneg_right hεc hlog0
    apply (le_div_iff₀ hln2).mpr
    have hh' := mul_le_mul_of_nonneg_right hdU hln2.le
    nlinarith
  have hpow : C^(width ε n) ≤ Real.sqrt n := by
    have he : C^(width ε n)=Real.exp ((width ε n : ℝ)*Real.log C) := by
      rw [Real.exp_nat_mul,Real.exp_log (by linarith : 0 < C)]
    have hs : Real.sqrt n=Real.exp ((1/2 : ℝ)*Real.log n) := by
      rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hnR]
      congr 1
      ring
    rw [he,hs]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hdU hlnC.le
    have hh' := mul_le_mul_of_nonneg_right hεC hlog0
    nlinarith
  have hg : (ε*(ε+3)/a)*(Real.log n)^3 ≤ Real.sqrt n := by
    simpa only [←Real.sqrt_eq_rpow] using hgrowth
  have hbase := P2MSelectorLiftExponentComparison.base_dominates a ε ha hε n (width ε n) (by omega)
    hd hlog hdU (C^(width ε n)) (pow_pos (by linarith : 0 < C) _) hpow hg
  have hlower : (n : ℝ)^((ε/2)*Real.log n) ≤ (n : ℝ)^(width ε n+1) := by
    rw [←Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega))
    have hf : ε*Real.log n < (width ε n : ℝ)+1 := Nat.lt_floor_add_one _
    push_cast
    nlinarith
  exact ⟨hn,hd,hdRange,hbase,hlower⟩

end SemAC02.Supplement.P2MSelectorLiftAsymptoticParameters
end

section
-- Inlined Solutions.P2MSelectorLiftSatisfiability

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MSelectorLiftSatisfiability

open LiftSAParity

theorem base_of_lift {n q : ℕ} (F : List (Clause (Fin n)))
    (hF : Satisfiable (selLift q F).toFinset) : Satisfiable F.toFinset := by
  classical
  obtain ⟨X,hX⟩ := hF
  have hchoose : ∀ i : Fin n, ∃ c : Bool×Fin q, X (i,c)=true := by
    intro i
    have hs := hX (Finset.univ.image (fun c : Bool×Fin q => ((i,c),true))) (by simp [selLift])
    by_contra hh
    push_neg at hh
    apply hs
    intro l hl
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hl
    exact hh c
  choose chosen hchosen using hchoose
  have huniq (i : Fin n) (c : Bool×Fin q) (hc : X (i,c)=true) : c=chosen i := by
    by_contra hne
    let S : Finset (Bool×Fin q) := {c,chosen i}
    have hcard : S.card=2 := by simp [S,hne]
    have hmem : S.image (fun c => ((i,c),false))∈selLift q F := by
      simp only [selLift,List.mem_append,List.mem_map,List.mem_flatMap]
      left; right
      refine ⟨i,by simp,S,?_,rfl⟩
      exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcard⟩)
    apply hX _ (List.mem_toFinset.mpr hmem)
    intro l hl
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hl
    have hd' : d=c ∨ d=chosen i := by simpa [S] using hd
    rcases hd' with rfl | rfl <;> simp [hc,hchosen]
  refine ⟨fun i => (chosen i).1,?_⟩
  intro C hC hbad
  let D := C.biUnion (fun l => Finset.univ.image (fun a : Fin q => ((l.1,l.2,a),true)))
  have hD : D∈selLift q F := by
    simp only [selLift,List.mem_append,List.mem_map]
    right
    exact ⟨C,List.mem_toFinset.mp hC,rfl⟩
  apply hX D (List.mem_toFinset.mpr hD)
  intro l hl
  obtain ⟨a,ha,hl⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hl
  intro htrue
  have he := huniq a.1 (a.2,j) htrue
  have hb := congrArg Prod.fst he
  exact hbad a ha hb.symm

theorem unsatisfiable_lift {n q : ℕ} (F : List (Clause (Fin n))) (hF : ¬ Satisfiable F.toFinset) :
    ¬ Satisfiable (selLift q F).toFinset := fun h => hF (base_of_lift F h)

end SemAC02.Supplement.P2MSelectorLiftSatisfiability
end

section
-- Inlined Solutions.P2MArithmeticCircuitBasics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MArithmeticCircuitBasics

open MvPolynomial ACirc

lemma toPoly_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) :
    toPoly (.sum ps) = (ps.map (fun p => C p.1*toPoly p.2)).sum := by
  rw [toPoly,List.attach_map_val (f := fun p : F × ACirc F V => C p.1*toPoly p.2)]

lemma toPoly_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) :
    toPoly (.prod cs) = (cs.map toPoly).prod := by
  rw [toPoly,List.attach_map_val]

lemma mem_fold_union {I : Type} [DecidableEq I] (a : I) (Ss : List (Finset I)) :
    a ∈ Ss.foldr (· ∪ ·) ∅ ↔ ∃ S ∈ Ss, a ∈ S := by
  induction Ss with
  | nil => simp
  | cons S Ss ih => simp only [List.foldr_cons,Finset.mem_union,ih,List.mem_cons]; aesop

lemma mem_subterms_prod {F V : Type} (a : ACirc F V) (cs : List (ACirc F V)) :
    a ∈ subterms (.prod cs) ↔ a = .prod cs ∨ ∃ c ∈ cs, a ∈ subterms c := by
  classical
  rw [subterms,List.attach_map_val (f := fun c : ACirc F V => subterms c),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma mem_subterms_sum {F V : Type} (a : ACirc F V) (ps : List (F × ACirc F V)) :
    a ∈ subterms (.sum ps) ↔ a = .sum ps ∨ ∃ p ∈ ps, a ∈ subterms p.2 := by
  classical
  rw [subterms,List.attach_map_val (f := fun p : F × ACirc F V => subterms p.2),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma self_mem_subterms {F V : Type} (c : ACirc F V) : c ∈ subterms c := by
  cases c with
  | var i => simp [subterms]
  | const a => simp [subterms]
  | sum ps => exact (mem_subterms_sum _ _).mpr (Or.inl rfl)
  | prod cs => exact (mem_subterms_prod _ _).mpr (Or.inl rfl)

lemma cval_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) (x : V → Bool) :
    cval (.sum ps) x = (ps.map (fun p => p.1*cval p.2 x)).sum := by
  simp only [cval,polyFn,toPoly_sum,map_list_sum,List.map_map,Function.comp_def,map_mul,eval_C]

lemma cval_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) (x : V → Bool) :
    cval (.prod cs) x = (cs.map (fun c => cval c x)).prod := by
  simp only [cval,polyFn,toPoly_prod,map_list_prod,List.map_map,Function.comp_def]

end SemAC02.Supplement.P2MArithmeticCircuitBasics
end

section
-- Inlined Solutions.P2MBottomMonomialSupport

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBottomMonomialSupport

open MvPolynomial ACirc P2MArithmeticCircuitBasics

noncomputable def leafExponent {F V : Type} (c : ACirc F V) : V →₀ ℕ :=
  match c with | .var i => Finsupp.single i 1 | _ => 0

def leafCoefficient {F V : Type} [Zero F] [One F] (c : ACirc F V) : F :=
  match c with | .var _ => 1 | .const a => a | _ => 0

noncomputable def exponent {F V : Type} (c : ACirc F V) : V →₀ ℕ :=
  match c with | .prod cs => (cs.map leafExponent).sum | _ => 0

def coefficient {F V : Type} [CommRing F] (c : ACirc F V) : F :=
  match c with | .prod cs => (cs.map leafCoefficient).prod | _ => 0

theorem leaf_poly {F V : Type} [CommRing F] (c : ACirc F V) (hc : IsLeaf c) :
    c.toPoly=monomial (leafExponent c) (leafCoefficient c) := by
  cases c with
  | var i => simp only [toPoly,leafExponent,leafCoefficient]; rfl
  | const a => simp only [toPoly,leafExponent,leafCoefficient]; rfl
  | sum ps => exact hc.elim
  | prod cs => exact hc.elim

theorem gate_poly {F V : Type} [CommRing F] (c : ACirc F V) (hc : IsMonGate ⊤ c) :
    c.toPoly=monomial (exponent c) (coefficient c) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | sum ps => exact hc.elim
  | prod cs =>
    change (ACirc.prod cs).toPoly=monomial (cs.map leafExponent).sum (cs.map leafCoefficient).prod
    rw [toPoly_prod]
    have hleaf := hc.2
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have ht : ∀ d∈cs, IsLeaf d := fun d hd => hleaf d (by simp [hd])
      simp only [List.map_cons,List.prod_cons,List.sum_cons]
      rw [leaf_poly c (hleaf c (by simp)),ih ⟨le_top,ht⟩ ht,monomial_mul]

theorem support_list_sum {F V : Type} [CommRing F] (ps : List (MvPolynomial V F))
    (d : V →₀ ℕ) (hd : d∈ps.sum.support) : ∃ p∈ps, d∈p.support := by
  classical
  induction ps with
  | nil => simp at hd
  | cons p ps ih =>
    rcases Finset.mem_union.mp (support_add hd) with hp | hp
    · exact ⟨p,by simp,hp⟩
    · obtain ⟨q,hq,hdq⟩ := ih hp
      exact ⟨q,by simp [hq],hdq⟩

theorem mlz_support {F V : Type} [CommRing F] (p : MvPolynomial V F)
    (s : V →₀ ℕ) (hs : s∈(mlz p).support) : ∃ d∈p.support, s=AC02Frege.sqfree d := by
  classical
  rw [mlz] at hs
  obtain ⟨d,hd,hsd⟩ := Finset.mem_biUnion.mp (support_sum hs)
  exact ⟨d,hd,Finset.mem_singleton.mp (support_monomial_subset hsd)⟩

theorem bottom_support {F V : Type} [CommRing F] (b : ACirc F V)
    (hb : IsSumOf (IsMonGate ⊤) b) (s : V →₀ ℕ) (hs : s∈(mlz b.toPoly).support) :
    ∃ c∈subterms b, s=AC02Frege.sqfree (exponent c) := by
  obtain ⟨d,hd,hsd⟩ := mlz_support b.toPoly s hs
  cases b with
  | var i => exact hb.elim
  | const a => exact hb.elim
  | prod cs => exact hb.elim
  | sum ps =>
    rw [toPoly_sum] at hd
    obtain ⟨q,hq,hdq⟩ := support_list_sum _ d hd
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    rw [gate_poly p.2 (hb p hp),C_mul_monomial] at hdq
    have he : d=exponent p.2 := Finset.mem_singleton.mp (support_monomial_subset hdq)
    exact ⟨p.2,(mem_subterms_sum _ _).mpr (Or.inr ⟨p,hp,self_mem_subterms _⟩),hsd.trans (congrArg AC02Frege.sqfree he)⟩

end SemAC02.Supplement.P2MBottomMonomialSupport
end

section
-- Inlined Solutions.P2MArithmeticProofCounts

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MArithmeticProofCounts

open ACirc

lemma csize_cons {F V : Type} (c : ACirc F V) (π : List (ACirc F V)) :
    csize (c::π) ≤ (subterms c).card+csize π := by
  classical
  unfold csize
  rw [List.toFinset_cons,Finset.biUnion_insert]
  exact Finset.card_union_le _ _

theorem csize_map_le {F V I : Type} (π : List I) (f : I → ACirc F V) (B : ℕ)
    (hf : ∀ i ∈ π, (subterms (f i)).card ≤ B) : csize (π.map f) ≤ π.length*B := by
  induction π with
  | nil => simp [csize]
  | cons i π ih =>
    have h := (csize_cons (f i) (π.map f)).trans (Nat.add_le_add
      (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj]))))
    simpa only [List.map_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using h

theorem topS_le_topOcc {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    topS Ω π ≤ topOcc π := by
  classical
  let ts := π.flatMap topTerms
  let G : Finset (Ω → F) := ts.toFinset.image (fun t => fun x : Ω => cval t x.1)
  have hsub : {g : Ω → F | g ≠ 0 ∧ ∃ c ∈ π, ∃ t ∈ topTerms c, g = fun x => cval t x.1} ⊆
      (↑G : Set (Ω → F)) := by
    rintro g ⟨hg,c,hc,t,ht,rfl⟩
    exact Finset.mem_image.mpr ⟨t,List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨c,hc,ht⟩),rfl⟩
  calc
    _ ≤ (↑G : Set (Ω → F)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet G)
    _ = G.card := Set.ncard_coe_finset _
    _ ≤ ts.toFinset.card := Finset.card_image_le
    _ ≤ ts.length := List.toFinset_card_le ts
    _ = _ := by simp only [ts,List.length_flatMap,topOcc]

end SemAC02.Supplement.P2MArithmeticProofCounts
end

section
-- Inlined Solutions.P2MBottomMonomialSize

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBottomMonomialSize

open ACirc P2MArithmeticCircuitBasics P2MBottomMonomialSupport

theorem bottom_parent {F V : Type} (c : ACirc F V) (hc : IsSPSP ⊤ c)
    (b : ACirc F V) (hb : b∈bottomPolys c) :
    IsSumOf (IsMonGate ⊤) b ∧ ∀ g∈subterms b, g∈subterms c := by
  cases c with
  | var i => simp [bottomPolys] at hb
  | const a => simp [bottomPolys] at hb
  | prod cs => simp [bottomPolys] at hb
  | sum ps =>
    obtain ⟨p,hp,hbp⟩ := List.mem_flatMap.mp hb
    have ht := hc p hp
    rcases p with ⟨a,t⟩
    cases t with
    | var i => exact ht.elim
    | const z => exact ht.elim
    | sum qs => exact ht.elim
    | prod cs =>
      change b∈cs at hbp
      refine ⟨ht b hbp,?_⟩
      intro g hg
      apply (mem_subterms_sum _ _).mpr
      exact Or.inr ⟨(a,.prod cs),hp,(mem_subterms_prod _ _).mpr (Or.inr ⟨b,hbp,hg⟩)⟩

theorem Mbot_le_csize {F V : Type} [CommRing F] (π : List (ACirc F V))
    (hπ : ∀ c∈π, IsSPSP ⊤ c) : Mbot π ≤ max 1 (csize π) := by
  classical
  let U := π.toFinset.biUnion subterms
  let E := (π.flatMap bottomPolys).toFinset.biUnion (fun b => (mlz b.toPoly).support)
  have hsub : E⊆U.image (fun c => AC02Frege.sqfree (exponent c)) := by
    intro s hs
    obtain ⟨b,hb,hs⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨c,hc,hbc⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hb)
    have hparent := bottom_parent c (hπ c hc) b hbc
    obtain ⟨g,hg,hsg⟩ := bottom_support b hparent.1 s hs
    exact Finset.mem_image.mpr ⟨g,Finset.mem_biUnion.mpr
      ⟨c,List.mem_toFinset.mpr hc,hparent.2 g hg⟩,hsg.symm⟩
  exact max_le_max_left 1 ((Finset.card_le_card hsub).trans Finset.card_image_le)

theorem csize_le_size4 {F V : Type} (π : List (ACirc F V)) : csize π ≤ size4 π := by
  induction π with
  | nil => simp [csize,size4]
  | cons c π ih =>
    have hh := P2MArithmeticProofCounts.csize_cons c π
    simpa only [size4,List.map_cons,List.sum_cons] using hh.trans (Nat.add_le_add_left ih _)

theorem Mbot_le_size4 {F V : Type} [CommRing F] (π : List (ACirc F V))
    (hπ : ∀ c∈π, IsSPSP ⊤ c) : Mbot π ≤ max 1 (size4 π) :=
  (Mbot_le_csize π hπ).trans (max_le_max_left 1 (csize_le_size4 π))

end SemAC02.Supplement.P2MBottomMonomialSize
end

section
-- Inlined Solutions.P2MProofTopFunctions

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MProofTopFunctions

open ACirc Classical

noncomputable def pool {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    Finset (Ω → F) :=
  ((π.flatMap topTerms).map (fun t => fun x : Ω => cval t x.1)).toFinset.filter (fun g => g≠0)

theorem mem_pool {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) (g : Ω → F) :
    g∈pool Ω π ↔ g≠0 ∧ ∃ c∈π, ∃ t∈topTerms c, (fun x : Ω => cval t x.1)=g := by
  constructor
  · intro hp
    have hn := (Finset.mem_filter.mp hp).2
    obtain ⟨t,ht,he⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
    obtain ⟨c,hc,ht⟩ := List.mem_flatMap.mp ht
    exact ⟨hn,c,hc,t,ht,he⟩
  · rintro ⟨hn,c,hc,t,ht,he⟩
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨t,List.mem_flatMap.mpr ⟨c,hc,ht⟩,he⟩),hn⟩

theorem card_eq_topS {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    (pool Ω π).card=topS Ω π := by
  have he : {g : Ω → F | g≠0 ∧ ∃ c∈π, ∃ t∈topTerms c, g=fun x => cval t x.1}=
      (↑(pool Ω π) : Set (Ω → F)) := by
    ext g
    rw [Finset.mem_coe,mem_pool]
    constructor
    · rintro ⟨hn,c,hc,t,ht,he⟩; exact ⟨hn,c,hc,t,ht,he.symm⟩
    · rintro ⟨hn,c,hc,t,ht,he⟩; exact ⟨hn,c,hc,t,ht,he.symm⟩
  unfold topS
  rw [he,Set.ncard_coe_finset]

theorem projection_bound {F V U : Type} [CommRing F]
    (η : (U → Bool) → (V → Bool)) (M τ : ACirc F V → ACirc F U)
    (π : List (ACirc F V))
    (hterms : ∀ c, topTerms (M c)=(topTerms c).map τ)
    (hval : ∀ c∈π, ∀ t∈topTerms c, ∀ y, cval (τ t) y=cval t (η y)) :
    topS Set.univ (π.map M) ≤ topS Set.univ π := by
  let pull (f : ↥(Set.univ : Set (V → Bool)) → F) : ↥(Set.univ : Set (U → Bool)) → F :=
    fun y => f ⟨η y.1,Set.mem_univ _⟩
  have hsub : pool Set.univ (π.map M)⊆(pool Set.univ π).image pull := by
    intro g hg
    obtain ⟨hn,c',hc',t',ht',he⟩ := (mem_pool Set.univ (π.map M) g).mp hg
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hc'
    rw [hterms c] at ht'
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp ht'
    let f : ↥(Set.univ : Set (V → Bool)) → F := fun x => cval t x.1
    have hpull : pull f=g := by
      rw [←he]
      funext y
      exact (hval c hc t ht y.1).symm
    have hf : f≠0 := by
      intro hz
      apply hn
      rw [←hpull,hz]
      rfl
    exact Finset.mem_image.mpr ⟨f,(mem_pool Set.univ π f).mpr ⟨hf,c,hc,t,ht,rfl⟩,hpull⟩
  rw [←card_eq_topS,←card_eq_topS]
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

end SemAC02.Supplement.P2MProofTopFunctions
end

section
-- Inlined Solutions.P2MArithmeticTopSize

namespace SemAC02.Supplement.P2MArithmeticTopSize

open ACirc P2MArithmeticCircuitBasics

theorem top_term_subterm {F V : Type} (c t : ACirc F V) (ht : t∈topTerms c) : t∈subterms c := by
  cases c with
  | var i => simp [topTerms] at ht
  | const a => simp [topTerms] at ht
  | prod cs => simp [topTerms] at ht
  | sum ps =>
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ht
    exact (mem_subterms_sum _ _).mpr (Or.inr ⟨p,hp,self_mem_subterms _⟩)

theorem top_le_csize {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    topS Ω π ≤ csize π := by
  classical
  let U := π.toFinset.biUnion subterms
  have hsub : P2MProofTopFunctions.pool Ω π⊆U.image (fun t => fun x : Ω => cval t x.1) := by
    intro g hg
    obtain ⟨hn,c,hc,t,ht,he⟩ := (P2MProofTopFunctions.mem_pool Ω π g).mp hg
    exact Finset.mem_image.mpr ⟨t,Finset.mem_biUnion.mpr
      ⟨c,List.mem_toFinset.mpr hc,top_term_subterm c t ht⟩,he⟩
  rw [←P2MProofTopFunctions.card_eq_topS]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end SemAC02.Supplement.P2MArithmeticTopSize
end

section
-- Inlined Solutions.P2MSelectorLiftSizeTransfer

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MSelectorLiftSizeTransfer

open ACirc

theorem lower_bound {𝔽 : Type} [Field 𝔽] {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d)
    (F : List (LiftSAParity.Clause (Fin n)))
    (hbase : ∀ π : List (ACirc 𝔽 (Fin n)),
      IsSemPCRef (IsSPSP (d : ℕ∞)) Set.univ (clauseAx {C | C∈F}) π → n^(d+1) ≤ topS Set.univ π)
    (π : List (ACirc 𝔽 (Fin n×Bool×Fin n)))
    (hπ : IsSemPCRef (IsSPSP ⊤) Set.univ (clauseAx {C | C∈selLift n F}) π) : n^(d+1) ≤ size4 π := by
  by_contra hh
  have hsmall : size4 π < n^(d+1) := lt_of_not_ge hh
  have hp : 1 < n^(d+1) := Nat.one_lt_pow (by omega) (by omega)
  have hM : Mbot π < n^(d+1) := (P2MBottomMonomialSize.Mbot_le_size4 π hπ.1).trans_lt
    (max_lt hp hsmall)
  obtain ⟨π',hπ',hTop,hLen,hOcc⟩ := (theorem_7_9_lifting_bounded_bottom hn F π hπ).1 d hd hM
  have hbound := (hbase π' hπ').trans hTop
  have hsize := (P2MArithmeticTopSize.top_le_csize Set.univ π).trans (P2MBottomMonomialSize.csize_le_size4 π)
  exact (not_lt_of_ge (hbound.trans hsize)) hsmall

end SemAC02.Supplement.P2MSelectorLiftSizeTransfer
end

section
-- Inlined Solutions.P2MUniformFiniteProbability

set_option maxHeartbeats 1000000

namespace ProofComplexity.P2MUniformFiniteProbability

open SemAC02.Supplement

attribute [local instance] Classical.propDecidable

theorem nonneg {A : Type} [Fintype A] (E : A → Prop) : 0 ≤ uprob E := by unfold uprob; positivity

theorem le_one {A : Type} [Fintype A] (E : A → Prop) : uprob E ≤ 1 := by
  classical
  unfold uprob
  apply div_le_one_of_le₀
  · exact_mod_cast (Finset.card_le_univ (Finset.univ.filter E))
  · positivity

theorem mono {A : Type} [Fintype A] (E F : A → Prop) (h : ∀ a, E a → F a) : uprob E ≤ uprob F := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hs : Finset.univ.filter E⊆Finset.univ.filter F := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h a (Finset.mem_filter.mp ha).2⟩
  exact_mod_cast Finset.card_le_card hs

theorem complement {A : Type} [Fintype A] [Nonempty A] (E : A → Prop) :
    uprob (fun a => ¬ E a)=1-uprob E := by
  classical
  have hc : ((Finset.univ.filter (fun a => ¬ E a)).card : ℝ)+
      ((Finset.univ.filter E).card : ℝ)=Fintype.card A := by
    have hh := Finset.card_filter_add_card_filter_not (s:=Finset.univ) E
    have hn : (Finset.univ.filter (fun a => ¬ E a)).card+(Finset.univ.filter E).card=Fintype.card A := by
      simpa only [Finset.card_univ,Nat.add_comm] using hh
    exact_mod_cast hn
  have hn : (Fintype.card A : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold uprob
  apply (eq_sub_iff_add_eq).mpr
  rw [Finset.filter_congr_decidable Finset.univ (fun a => ¬ E a) (Classical.decPred _)]
  rw [←add_div,hc,div_self hn]

theorem union_bound {A I : Type} [Fintype A] (S : Finset I) (E : A → Prop) (F : I → A → Prop)
    (h : ∀ a, E a → ∃ i∈S, F i a) : uprob E ≤ ∑ i∈S, uprob (F i) := by
  classical
  have hsub : Finset.univ.filter E⊆S.biUnion (fun i => Finset.univ.filter (F i)) := by
    intro a ha
    obtain ⟨i,hi,hFi⟩ := h a (Finset.mem_filter.mp ha).2
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hFi⟩⟩
  have hc : ((Finset.univ.filter E).card : ℝ) ≤ ∑ i∈S, ((Finset.univ.filter (F i)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  unfold uprob
  rw [←Finset.sum_div]
  exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)

noncomputable def productEventEquiv {A I : Type} (E : I → A → Prop) :
    {f : I → A // ∀ i, E i (f i)} ≃ ((i : I) → {a : A // E i a}) where
  toFun f i := ⟨f.1 i,f.2 i⟩
  invFun f := ⟨fun i => (f i).1,fun i => (f i).2⟩
  left_inv f := rfl
  right_inv f := rfl

theorem independent {A I : Type} [Fintype A] [Fintype I] [DecidableEq I] (E : I → A → Prop) :
    uprob (fun f : I → A => ∀ i, E i (f i))=∏ i, uprob (E i) := by
  classical
  have hc : ((Finset.univ.filter (fun f : I → A => ∀ i, E i (f i))).card : ℝ)=
      ∏ i, ((Finset.univ.filter (E i)).card : ℝ) := by
    rw [←Fintype.card_subtype,Fintype.card_congr (productEventEquiv E),Fintype.card_pi]
    simp only [Nat.cast_prod,Fintype.card_subtype]
  unfold uprob
  rw [Finset.filter_congr_decidable Finset.univ (fun f : I → A => ∀ i, E i (f i)) (Classical.decPred _)]
  rw [hc,Finset.prod_div_distrib]
  congr 1
  simp

theorem congr {A : Type} [Fintype A] (E F : A → Prop) (h : ∀ a, E a ↔ F a) : uprob E=uprob F :=
  le_antisymm (mono E F (fun a => (h a).mp)) (mono F E (fun a => (h a).mpr))

theorem true_event {A : Type} [Fintype A] [Nonempty A] : uprob (fun _ : A => True)=1 := by
  simp [uprob,Fintype.card_ne_zero]

theorem equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (E : B → Prop) :
    uprob (fun a => E (e a))=uprob E := by
  classical
  unfold uprob
  rw [Fintype.card_congr e]
  congr 1
  apply congrArg Nat.cast
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
  · intro a ha b hb he
    exact e.injective he
  · intro b hb
    exact ⟨e.symm b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using (Finset.mem_filter.mp hb).2⟩,e.apply_symm_apply b⟩

theorem coordinates {A I : Type} [Fintype A] [Nonempty A] [Fintype I] [DecidableEq I]
    (J : Finset I) (E : A → Prop) :
    uprob (fun f : I → A => ∀ i∈J, E (f i))=(uprob E)^J.card := by
  classical
  rw [independent (fun i a => i∈J → E a)]
  have he (i : I) : uprob (fun a => i∈J → E a)=if i∈J then uprob E else 1 := by
    by_cases hi : i∈J
    · rw [if_pos hi]
      exact congr _ _ (fun a => by simp [hi])
    · rw [if_neg hi]
      exact (congr _ _ (fun a => by simp [hi])).trans true_event
  simp only [he]
  rw [←Finset.prod_filter]
  have hfilter : (Finset.univ : Finset I).filter (· ∈ J)=J := by ext i; simp
  rw [hfilter,Finset.prod_const]

theorem intersection_lower {A : Type} [Fintype A] [Nonempty A] (E F : A → Prop) :
    uprob E+uprob F-1 ≤ uprob (fun a => E a ∧ F a) := by
  classical
  have hb := union_bound (Finset.univ : Finset Bool) (fun a => ¬ (E a ∧ F a))
    (fun b a => if b then ¬ E a else ¬ F a) (by
      intro a ha
      by_cases he : E a
      · exact ⟨false,Finset.mem_univ _,by simpa using (fun hf => ha ⟨he,hf⟩)⟩
      · exact ⟨true,Finset.mem_univ _,by simpa using he⟩)
  have hh : uprob (fun a => ¬ (E a ∧ F a)) ≤ uprob (fun a => ¬ E a)+uprob (fun a => ¬ F a) := by
    simpa [Bool.forall_bool,add_comm] using hb
  rw [complement,complement,complement] at hh
  linarith

end ProofComplexity.P2MUniformFiniteProbability
end

section
-- Inlined Solutions.P2MRandomSelectorLiftLowerBound

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MRandomSelectorLiftLowerBound

open ACirc Filter Topology ProofComplexity.P2MUniformFiniteProbability

theorem full :
    (∀ n : ℕ, Fintype.card (Fin n × Bool × Fin n) = 2 * n ^ 2) ∧
    (∃ K : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ ω : Fin (n * 2 ^ Nat.clog 2 n) → WClause n (Nat.clog 2 n),
        ((selLift n (List.ofFn (fun j => (ω j).1))).length : ℝ) ≤ K * (n : ℝ) ^ 3 ∧
        (((selLift n (List.ofFn (fun j => (ω j).1))).map Finset.card).sum : ℝ) ≤
          K * (n : ℝ) ^ 3 * Real.log n) ∧
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => uprob
        (fun ω : Fin (n * 2 ^ Nat.clog 2 n) → WClause n (Nat.clog 2 n) =>
          ¬ LiftSAParity.Satisfiable (selLift n (List.ofFn (fun j => (ω j).1))).toFinset ∧
          ∀ π : List (ACirc (ZMod 2) (Fin n × Bool × Fin n)),
            IsSemPCRef (IsSPSP ⊤) Set.univ
              (clauseAx {C | C ∈ selLift n (List.ofFn (fun j => (ω j).1))}) π →
            (n : ℝ) ^ (c * Real.log n) ≤ size4 π)) atTop (𝓝 1)  := by
  refine ⟨P2MRandomSelectorLiftCounts.variable_count, ?_, ?_⟩
  · exact ⟨16/Real.log 2,2,fun n hn ω => P2MRandomSelectorLiftCounts.bounds n hn ω⟩
  obtain ⟨a,C,c,ha,hC,hc,hBase⟩ := theorem_7_2_random_log_width
  obtain ⟨ε,hε,hParameters⟩ := P2MSelectorLiftAsymptoticParameters.eventually_valid a C c ha hC hc
  refine ⟨ε/2,by positivity,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hBase tendsto_const_nhds _
    (Filter.Eventually.of_forall (fun n => le_one _))
  filter_upwards [hParameters] with n hp
  rcases hp with ⟨hn,hd,hRange,hDom,hLower⟩
  apply mono
  rintro ω ⟨hUnsat,hSmall⟩
  let F := List.ofFn (fun j => (ω j).1)
  have hF : F.toFinset=seqCNF ω := by
    ext D
    simp [F,seqCNF,List.mem_ofFn]
  have hAx : {D | D∈F}=(seqCNF ω : Set (LiftSAParity.Clause (Fin n))) := by
    ext D
    simp [F,seqCNF,List.mem_ofFn]
  refine ⟨P2MSelectorLiftSatisfiability.unsatisfiable_lift F (by simpa only [hF] using hUnsat),?_⟩
  intro π hπ
  have hbase : ∀ π' : List (ACirc (ZMod 2) (Fin n)),
      IsSemPCRef (IsSPSP (P2MSelectorLiftAsymptoticParameters.width ε n : ℕ∞)) Set.univ
        (clauseAx {D | D∈F}) π' → n^(P2MSelectorLiftAsymptoticParameters.width ε n+1) ≤ topS Set.univ π' := by
    intro π' hπ'
    rw [hAx] at hπ'
    have hh := (hSmall _ hd hRange π' hπ').1
    have hb := hDom.trans hh
    exact_mod_cast hb
  have hs := P2MSelectorLiftSizeTransfer.lower_bound hn hd F hbase π hπ
  apply hLower.trans
  exact_mod_cast hs

end SemAC02.Supplement.P2MRandomSelectorLiftLowerBound
end

end P2MRandomSelectorLiftProof
open SemAC02.Supplement MvPolynomial ACirc Filter Topology

theorem solution :
    (∀ n : ℕ, Fintype.card (Fin n × Bool × Fin n) = 2 * n ^ 2) ∧
    (∃ K : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ ω : Fin (n * 2 ^ Nat.clog 2 n) → WClause n (Nat.clog 2 n),
        ((selLift n (List.ofFn (fun j => (ω j).1))).length : ℝ) ≤ K * (n : ℝ) ^ 3 ∧
        (((selLift n (List.ofFn (fun j => (ω j).1))).map Finset.card).sum : ℝ) ≤
          K * (n : ℝ) ^ 3 * Real.log n) ∧
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => uprob
        (fun ω : Fin (n * 2 ^ Nat.clog 2 n) → WClause n (Nat.clog 2 n) =>
          ¬ LiftSAParity.Satisfiable (selLift n (List.ofFn (fun j => (ω j).1))).toFinset ∧
          ∀ π : List (ACirc (ZMod 2) (Fin n × Bool × Fin n)),
            IsSemPCRef (IsSPSP ⊤) Set.univ
              (clauseAx {C | C ∈ selLift n (List.ofFn (fun j => (ω j).1))}) π →
            (n : ℝ) ^ (c * Real.log n) ≤ size4 π)) atTop (𝓝 1)  := by
  exact P2MRandomSelectorLiftProof.SemAC02.Supplement.P2MRandomSelectorLiftLowerBound.full
