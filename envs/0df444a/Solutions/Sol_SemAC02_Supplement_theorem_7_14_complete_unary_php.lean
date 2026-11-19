-- Prove2me | solution 1 for SemAC02.Supplement.theorem_7_14_complete_unary_php
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T14:47:53.308334+00:00
-- url     : https://prove2.me/submissions/b8203ef7-db3d-4a0b-a316-430336b2bf97

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_SemAC02_Supplement_phpG
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_AC02Frege_ML
import Definitions.Def_SemAC02_nDivision
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_bernProb
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_PCNonBool_boundaryOn
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_SemAC02_Supplement_expansionRank
import Definitions.Def_PCNonBool_BipGraph
import Theorems.Thm_SemAC02_Supplement_theorem_7_5_graph_php_bounded_bottom

open _root_.SemAC02 _root_.SemAC02.Supplement
open _root_.AC02Frege
namespace P2MCompleteUnaryPHPProof
section
-- Inlined Solutions.P2MGraphSparsificationSurvivalNumerics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphSparsificationSurvivalNumerics

 theorem bound (γ β δ ξ : ℝ) (hβ : 0 < β) (hξ : 0 < ξ) (hδ : δ < 1)
    (hgap : γ-β+β*δ ≤ -ξ) (n Δ w : ℕ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ)
    (hL : 1 ≤ Real.log n) (hH : 0 < Real.log (Real.log n))
    (hHL : Real.log (Real.log n) ≤ Real.log n)
    (hDlog : Real.log (Δ : ℝ) ≤ δ*Real.log n)
    (hw : β*Real.log n/Real.log (Real.log n) ≤ (w : ℝ)+1) :
    Real.exp (γ*Real.log n^2/Real.log (Real.log n))*((Δ : ℝ)/n)^(w+1) ≤
      Real.exp (-ξ*Real.log n) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hΔR : (0 : ℝ)<Δ := by exact_mod_cast (show 0 < Δ by omega)
  let L := Real.log (n : ℝ)
  let H := Real.log L
  let p := (Δ : ℝ)/n
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hp0 : 0 < p := div_pos hΔR hnR
  have hlogp : Real.log p ≤ -(1-δ)*L := by
    dsimp [p]
    rw [Real.log_div hΔR.ne' hnR.ne']
    dsimp [L]
    nlinarith
  have hlogp0 : Real.log p ≤ 0 := by nlinarith
  have hq : L ≤ L^2/H := (le_div_iff₀ hH).mpr (by
    have hh := mul_le_mul_of_nonneg_left hHL hL0
    dsimp [L,H] at *
    nlinarith)
  have hpow : p^(w+1)=Real.exp (((w : ℝ)+1)*Real.log p) := by
    simpa only [Nat.cast_add,Nat.cast_one,Real.exp_log hp0] using (Real.exp_nat_mul (Real.log p) (w+1)).symm
  change Real.exp (γ*L^2/H)*p^(w+1) ≤ _
  rw [hpow,←Real.exp_add]
  have hWLog := mul_le_mul_of_nonpos_right hw hlogp0
  have hWupper := mul_le_mul_of_nonneg_left hlogp (show 0 ≤ β*L/H by positivity)
  calc
    _ ≤ Real.exp (γ*L^2/H+(β*L/H)*(-(1-δ)*L)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = Real.exp ((γ-β+β*δ)*(L^2/H)) := by congr 1; field_simp <;> ring
    _ ≤ Real.exp ((-ξ)*(L^2/H)) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hgap (by positivity))
    _ ≤ Real.exp (-ξ*Real.log n) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hq (by linarith))

end SemAC02.Supplement.P2MGraphSparsificationSurvivalNumerics
end

section
-- Inlined Solutions.P2MGraphSparsificationDenominatorNumerics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphSparsificationDenominatorNumerics

 theorem bound (C β δ : ℝ) (hC : 0 < C) (hβ : 0 < β) (hδ : 0 < δ)
    (hSlack : 4*δ ≤ 1/2-β) (n Δ w : ℕ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ) (hw : 1 ≤ w) (hwΔ : w ≤ Δ)
    (hL : 1 ≤ Real.log n) (hH : 1 ≤ Real.log (Real.log n))
    (hDlog : Real.log (Δ : ℝ) ≤ δ*Real.log n)
    (hDnear : Real.log (Δ : ℝ) ≤ Real.log 49+Real.log (Real.log n))
    (hwU : (w : ℝ) ≤ β*Real.log n/Real.log (Real.log n))
    (hHlarge : β*(|Real.log C|+2*Real.log 49) ≤ 2*δ*Real.log (Real.log n)) :
    (w : ℝ)*Δ*(C*(Δ : ℝ)^2)^w ≤ (n : ℝ)^(β+1/2) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hΔR : (0 : ℝ)<Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hwR : (0 : ℝ)<w := by exact_mod_cast (show 0 < w by omega)
  let L := Real.log (n : ℝ)
  let H := Real.log L
  let A := |Real.log C|+2*Real.log 49
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hH0 : 0 < H := by dsimp [H,L]; linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlogw : Real.log (w : ℝ) ≤ δ*L := by
    apply (Real.log_le_log hwR (by exact_mod_cast hwΔ)).trans hDlog
  have hLogBase : Real.log (C*(Δ : ℝ)^2) ≤ 2*H+A := by
    rw [Real.log_mul hC.ne' (pow_ne_zero _ hΔR.ne'),Real.log_pow]
    dsimp [A,H,L]
    have hh := le_abs_self (Real.log C)
    nlinarith
  have hAH : β*A/H ≤ 2*δ := (div_le_iff₀ hH0).mpr (by nlinarith)
  have hWBase : (w : ℝ)*Real.log (C*(Δ : ℝ)^2) ≤ 2*β*L+2*δ*L := by
    have h1 := mul_le_mul_of_nonneg_left hLogBase (Nat.cast_nonneg (α:=ℝ) w)
    have h2 := mul_le_mul_of_nonneg_right hwU (show 0 ≤ 2*H+A by positivity)
    have he : (β*L/H)*(2*H+A)=2*β*L+(β*A/H)*L := by field_simp <;> ring
    rw [he] at h2
    have h3 := mul_le_mul_of_nonneg_right hAH hL0
    linarith
  let d := (w : ℝ)*Δ*(C*(Δ : ℝ)^2)^w
  have hd : 0 < d := by dsimp [d]; positivity
  have hLogD : Real.log d=Real.log (w : ℝ)+Real.log (Δ : ℝ)+(w : ℝ)*Real.log (C*(Δ : ℝ)^2) := by
    dsimp [d]
    rw [Real.log_mul (mul_pos hwR hΔR).ne' (pow_ne_zero _ (by positivity : C*(Δ : ℝ)^2≠0)),
      Real.log_mul hwR.ne' hΔR.ne',Real.log_pow]
  have hBound : Real.log d ≤ (β+1/2)*L := by
    rw [hLogD]
    have hh := mul_le_mul_of_nonneg_right hSlack hL0
    dsimp [L] at *
    nlinarith
  change d ≤ _
  rw [←Real.exp_log hd,Real.rpow_def_of_pos hnR]
  apply Real.exp_le_exp.mpr
  nlinarith

end SemAC02.Supplement.P2MGraphSparsificationDenominatorNumerics
end

section
-- Inlined Solutions.P2MGraphSparsificationDominanceNumerics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphSparsificationDominanceNumerics

 theorem bound (a γ β d : ℝ) (ha : 0 < a) (hγ : 0 ≤ γ) (hd : 0 < d) (n : ℕ) (hn : 1 ≤ n)
    (hL : 1 ≤ Real.log n) (hH : 1 ≤ Real.log (Real.log n))
    (hdU : d ≤ (n : ℝ)^(β+1/2))
    (hGrowth : ((γ+2)/a)*Real.log n^2 ≤ (n : ℝ)^(1/2-β)) :
    Real.exp (γ*Real.log n^2/Real.log (Real.log n)) ≤ 1/4*Real.exp (a*n/d) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  let L := Real.log (n : ℝ)
  let H := Real.log L
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hHL : γ*L^2/H ≤ γ*L^2 := div_le_self (by positivity) hH
  have hX : 2+γ*L^2/H ≤ a*(n : ℝ)^(1/2-β) := by
    have hh := mul_le_mul_of_nonneg_left hGrowth ha.le
    have he : a*(((γ+2)/a)*L^2)=(γ+2)*L^2 := by field_simp
    rw [he] at hh
    have hLsq : 1 ≤ L^2 := by dsimp [L]; nlinarith
    nlinarith
  have hProd : d*(2+γ*L^2/H) ≤ a*n := by
    calc
      _ ≤ (n : ℝ)^(β+1/2)*(a*(n : ℝ)^(1/2-β)) :=
        mul_le_mul hdU hX (by positivity) (Real.rpow_nonneg hnR.le _)
      _ = a*((n : ℝ)^(β+1/2)*(n : ℝ)^(1/2-β)) := by ring
      _ = a*(n : ℝ)^((β+1/2)+(1/2-β)) := by rw [←Real.rpow_add hnR]
      _ = a*n := by rw [show (β+1/2)+(1/2-β)=(1 : ℝ) by ring,Real.rpow_one]
  have hExp : 2+γ*L^2/H ≤ a*n/d := (le_div_iff₀ hd).mpr (by nlinarith)
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have he := Real.add_one_le_exp (1 : ℝ)
    have he' : (Real.exp 1)^2=Real.exp 2 := by rw [←Real.exp_nat_mul]; congr 1; norm_num
    nlinarith
  calc
    _ ≤ 1/4*(Real.exp 2*Real.exp (γ*L^2/H)) := by nlinarith [Real.exp_pos (γ*L^2/H)]
    _ = 1/4*Real.exp (2+γ*L^2/H) := by rw [Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) (by norm_num)

end SemAC02.Supplement.P2MGraphSparsificationDominanceNumerics
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
-- Inlined Solutions.P2MPHPDeltaLogBounds

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPHPDeltaLogBounds

open Filter Topology

 theorem upper (n : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ Real.log n) : (php74Delta n : ℝ) ≤ 49*Real.log n := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2); linarith
  have he : Real.log (2*(n : ℝ))=Real.log 2+Real.log n := Real.log_mul (by norm_num) hnR.ne'
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 24*Real.log (2*(n : ℝ)) by rw [he]; positivity)
  change (⌈24*Real.log (2*(n : ℝ))⌉₊ : ℝ) ≤ 49*Real.log n
  rw [he] at hh ⊢
  linarith

 theorem eventually_scaled_log_log_le (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A*Real.log (Real.log n) ≤ Real.log n := by
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := ((Real.isLittleO_log_id_atTop).const_mul_left A).bound (by norm_num : (0 : ℝ)<1)
  filter_upwards [hl.eventually hh,ProofComplexity.P2MLogGrowth.eventually_log_large 0] with n hn hL
  have he : |A*Real.log (Real.log n)| ≤ Real.log n := by
    simpa only [Real.norm_eq_abs,one_mul,Function.comp_apply,id_eq,abs_of_nonneg hL] using hn
  exact (le_abs_self _).trans he

 theorem eventually_log_log_large (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A ≤ Real.log (Real.log n) :=
  (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))).eventually_ge_atTop A

end SemAC02.Supplement.P2MPHPDeltaLogBounds
end

section
-- Inlined Solutions.P2MGraphPHPParameters

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphPHPParameters

noncomputable def degree (n Δ : ℕ) : ℕ := ⌊(n : ℝ)/(4096*Δ)⌋₊
noncomputable def supportSize (n Δ : ℕ) : ℕ := ⌊(n : ℝ)/(4*Δ)⌋₊

 theorem finite_data (n Δ : ℕ) (hn : 128 ≤ n) (hΔ : 1 ≤ Δ)
    (hlarge : 32768*(Δ : ℝ)^2 ≤ n) :
    Δ ≤ n ∧ 1 ≤ degree n Δ ∧ 2*Δ ≤ degree n Δ ∧ 6*degree n Δ ≤ n ∧
      1 ≤ supportSize n Δ ∧ ((6*degree n Δ : ℕ) : ℝ)+2 ≤ (Δ : ℝ)*(supportSize n Δ)/8 ∧
      (n : ℝ)/(8192*Δ) ≤ degree n Δ ∧ (degree n Δ : ℝ)/n ≤ 1/64 := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hΔR : (0 : ℝ)<Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hΔ1 : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hn128 : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hΔSmall : (Δ : ℝ) ≤ (n : ℝ)/128 := by nlinarith [sq_nonneg ((Δ : ℝ)-1)]
  have hDiv : 4*(Δ : ℝ) ≤ (n : ℝ)/(8192*Δ) :=
    (le_div_iff₀ (by positivity : (0 : ℝ)<8192*Δ)).mpr (by nlinarith)
  have hkU : (degree n Δ : ℝ) ≤ (n : ℝ)/(4096*Δ) := Nat.floor_le (by positivity)
  have hkf : (n : ℝ)/(4096*Δ)-1 < (degree n Δ : ℝ) := Nat.sub_one_lt_floor _
  have he : (n : ℝ)/(4096*Δ)=2*((n : ℝ)/(8192*Δ)) := by ring
  have hkL : (n : ℝ)/(8192*Δ) ≤ degree n Δ := by rw [he] at hkf; nlinarith
  have hk2Δ : 2*Δ ≤ degree n Δ := by
    have hh : (2 : ℝ)*Δ ≤ degree n Δ := by linarith
    exact_mod_cast hh
  have hk1 : 1 ≤ degree n Δ := by omega
  have hkMult := (le_div_iff₀ (show (0 : ℝ)<4096*Δ by positivity)).mp hkU
  have hΔk : (degree n Δ : ℝ) ≤ (Δ : ℝ)*(degree n Δ : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ (Δ : ℝ)-1 by linarith) (Nat.cast_nonneg (α:=ℝ) (degree n Δ))]
  have hkUn : (degree n Δ : ℝ) ≤ (n : ℝ)/4096 := by nlinarith
  have hk6 : 6*degree n Δ ≤ n := by
    have hh : (6 : ℝ)*(degree n Δ : ℝ) ≤ n := by nlinarith
    exact_mod_cast hh
  have hsL : (n : ℝ)/4-Δ ≤ (Δ : ℝ)*supportSize n Δ := by
    have hf : (n : ℝ)/(4*Δ)-1 < (supportSize n Δ : ℝ) := Nat.sub_one_lt_floor _
    have hh := mul_lt_mul_of_pos_left hf hΔR
    have he : (Δ : ℝ)*((n : ℝ)/(4*Δ)-1)=(n : ℝ)/4-Δ := by field_simp <;> ring
    rw [he] at hh
    exact hh.le
  have hbudget : ((6*degree n Δ : ℕ) : ℝ)+2 ≤ (Δ : ℝ)*(supportSize n Δ)/8 := by
    push_cast
    nlinarith
  have hs1 : 1 ≤ supportSize n Δ := by
    by_contra hh
    have hz : supportSize n Δ=0 := by omega
    rw [hz,Nat.cast_zero,mul_zero,zero_div] at hbudget
    have hk0 := Nat.cast_nonneg (α:=ℝ) (6*degree n Δ)
    linarith
  have hDn : Δ ≤ n := by
    have hh : (Δ : ℝ) ≤ n := by linarith
    exact_mod_cast hh
  have hp : (degree n Δ : ℝ)/n ≤ 1/64 := (div_le_iff₀ hnR).mpr (by nlinarith)
  exact ⟨hDn,hk1,hk2Δ,hk6,hs1,hbudget,hkL,hp⟩

end SemAC02.Supplement.P2MGraphPHPParameters
end

section
-- Inlined Solutions.P2MGraphPHPAsymptoticParameters

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphPHPAsymptoticParameters

open Filter

 theorem eventual_data : ∀ᶠ n : ℕ in atTop,
    128 ≤ n ∧ 1 ≤ php74Delta n ∧ 24*Real.log n ≤ (php74Delta n : ℝ) ∧
      1 ≤ Real.log n ∧ 1 ≤ Real.log (Real.log n) ∧
      php74Delta n ≤ n ∧ 1 ≤ P2MGraphPHPParameters.degree n (php74Delta n) ∧
      2*php74Delta n ≤ P2MGraphPHPParameters.degree n (php74Delta n) ∧
      6*P2MGraphPHPParameters.degree n (php74Delta n) ≤ n ∧
      1 ≤ P2MGraphPHPParameters.supportSize n (php74Delta n) ∧
      ((6*P2MGraphPHPParameters.degree n (php74Delta n) : ℕ) : ℝ)+2 ≤
        (php74Delta n : ℝ)*(P2MGraphPHPParameters.supportSize n (php74Delta n))/8 ∧
      (n : ℝ)/(8192*php74Delta n) ≤ P2MGraphPHPParameters.degree n (php74Delta n) ∧
      (P2MGraphPHPParameters.degree n (php74Delta n) : ℝ)/n ≤ 1/64 := by
  have hgrowth := ProofComplexity.P2MLogGrowth.eventually_log_power_le (32768*49^2) 2 (C:=1) (by norm_num)
  have hlog := ProofComplexity.P2MLogGrowth.eventually_log_large 1
  have hloglog := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))).eventually_ge_atTop 1
  filter_upwards [hgrowth,hlog,hloglog,eventually_ge_atTop 128] with n hg hl hll hn
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2); linarith
  have hsum : Real.log (2*(n : ℝ))=Real.log 2+Real.log n := Real.log_mul (by norm_num) hnR.ne'
  have hLower : 24*Real.log n ≤ (php74Delta n : ℝ) := by
    have hh := Nat.le_ceil (24*Real.log (2*(n : ℝ)))
    rw [hsum] at hh
    change 24*Real.log n ≤ (⌈24*Real.log (2*(n : ℝ))⌉₊ : ℝ)
    rw [hsum]
    linarith
  have hD1 : 1 ≤ php74Delta n := by
    have hh : (1 : ℝ) ≤ php74Delta n := by linarith
    exact_mod_cast hh
  have hUpper : (php74Delta n : ℝ) ≤ 49*Real.log n := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 24*Real.log (2*(n : ℝ)) by rw [hsum]; positivity)
    change (⌈24*Real.log (2*(n : ℝ))⌉₊ : ℝ) ≤ 49*Real.log n
    rw [hsum] at hh ⊢
    linarith
  have hlarge : 32768*(php74Delta n : ℝ)^2 ≤ n := by
    simp only [Real.rpow_one] at hg
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (php74Delta n)) hUpper 2
    nlinarith
  rcases P2MGraphPHPParameters.finite_data n (php74Delta n) hn hD1 hlarge with
    ⟨hDn,hk,hDk,hkn,hs,hBudget,hkL,hp⟩
  exact ⟨hn,hD1,hLower,hl,hll,hDn,hk,hDk,hkn,hs,hBudget,hkL,hp⟩

 theorem width_bound (n w : ℕ) (hl : 1 ≤ Real.log n) (hll : 1 ≤ Real.log (Real.log n))
    (hD : 24*Real.log n ≤ (php74Delta n : ℝ))
    (hw : (w : ℝ) ≤ Real.log n/Real.log (Real.log n)) : w ≤ php74Delta n := by
  have hh : Real.log n/Real.log (Real.log n) ≤ Real.log n := div_le_self (by linarith) hll
  have hwr : (w : ℝ) ≤ php74Delta n := by linarith
  exact_mod_cast hwr

end SemAC02.Supplement.P2MGraphPHPAsymptoticParameters
end

section
-- Inlined Solutions.P2MGraphSparsificationAsymptoticParameters

set_option maxHeartbeats 4000000

namespace SemAC02.Supplement.P2MGraphSparsificationAsymptoticParameters

open Filter Topology

noncomputable def width (β : ℝ) (n : ℕ) : ℕ := ⌊β*Real.log n/Real.log (Real.log n)⌋₊

 theorem eventually_valid (a C γ : ℝ) (ha : 0 < a) (hC : 0 < C) (hγ : 0 < γ) (hγHalf : γ < 1/2) :
    ∃ w : ℕ → ℕ, ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 1 ≤ php74Delta n ∧ php74Delta n ≤ n ∧ 24*Real.log n ≤ (php74Delta n : ℝ) ∧
      1 ≤ w n ∧ (w n : ℝ) ≤ Real.log n/Real.log (Real.log n) ∧
      Real.exp (γ*Real.log n^2/Real.log (Real.log n))*((php74Delta n : ℝ)/n)^(w n+1)+7/(n : ℝ)^3<1 ∧
      Real.exp (γ*Real.log n^2/Real.log (Real.log n)) ≤
        1/4*Real.exp (a*n/((w n : ℝ)*php74Delta n*(C*(php74Delta n : ℝ)^2)^(w n))) := by
  let β := (γ+1/2)/2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hγβ : γ < β := by dsimp [β]; linarith
  have hβHalf : β < 1/2 := by dsimp [β]; linarith
  let ξ := (β-γ)/2
  let r := 1/2-β
  have hξ : 0 < ξ := by dsimp [ξ]; linarith
  have hr : 0 < r := by dsimp [r]; linarith
  let δ := min (ξ/β) (r/4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδSlack : 4*δ ≤ 1/2-β := by
    change 4*δ ≤ r
    have hh : δ ≤ r/4 := min_le_right (ξ/β) (r/4)
    linarith
  have hδ1 : δ < 1 := by linarith
  have hgap : γ-β+β*δ ≤ -ξ := by
    have hh := (le_div_iff₀ hβ).mp (min_le_left (ξ/β) (r/4))
    dsimp [δ,ξ] at *
    nlinarith
  let A := |Real.log C|+2*Real.log 49
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hLlarge := ProofComplexity.P2MLogGrowth.eventually_log_large (max 1 (Real.log 4/ξ))
  have hHlarge := P2MPHPDeltaLogBounds.eventually_log_log_large (max 1 (β*A/(2*δ)))
  have hDeltaGrowth := ProofComplexity.P2MLogGrowth.eventually_log_power_le 49 1 (C:=δ) hδ
  have hGrowth := ProofComplexity.P2MLogGrowth.eventually_log_power_le ((γ+2)/a) 2 (C:=r) hr
  have hWidth := P2MPHPDeltaLogBounds.eventually_scaled_log_log_le (2/β)
  refine ⟨width β,?_⟩
  filter_upwards [P2MGraphPHPAsymptoticParameters.eventual_data,hLlarge,hHlarge,hDeltaGrowth,hGrowth,hWidth]
    with n hParams hLlarge hHlarge hDeltaGrowth hGrowth hWidth
  rcases hParams with ⟨hn128,hΔ,hΔlog,hL1,hH1,hΔn,hRest⟩
  have hn : 1 ≤ n := by omega
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hΔR : (0 : ℝ)<php74Delta n := by exact_mod_cast (show 0 < php74Delta n by omega)
  let L := Real.log (n : ℝ)
  let H := Real.log L
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hH0 : 0 < H := by dsimp [H,L]; linarith
  have hHL : H ≤ L := by
    have hh := Real.log_le_sub_one_of_pos hL0
    dsimp [H]
    linarith
  have hDeltaUpper := P2MPHPDeltaLogBounds.upper n hn hL1
  have hDnear : Real.log (php74Delta n : ℝ) ≤ Real.log 49+H := by
    have hh := Real.log_le_log hΔR hDeltaUpper
    rw [Real.log_mul (by norm_num) hL0.ne'] at hh
    exact hh
  have hDpower : (php74Delta n : ℝ) ≤ (n : ℝ)^δ := by
    apply hDeltaUpper.trans
    simpa only [pow_one] using hDeltaGrowth
  have hDlog : Real.log (php74Delta n : ℝ) ≤ δ*L := by
    have hh := Real.log_le_log hΔR hDpower
    rwa [Real.log_rpow hnR] at hh
  have hwidthLarge : 2 ≤ β*L/H := by
    have hh := mul_le_mul_of_nonneg_left hWidth hβ.le
    have he : β*((2/β)*H)=2*H := by field_simp
    rw [he] at hh
    exact (le_div_iff₀ hH0).mpr (by nlinarith)
  have hw : 1 ≤ width β n := Nat.le_floor (by norm_num; linarith)
  have hwU : (width β n : ℝ) ≤ β*L/H := Nat.floor_le (by positivity)
  have hwL : β*L/H ≤ (width β n : ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hwRange : (width β n : ℝ) ≤ L/H := by
    apply hwU.trans
    apply div_le_div_of_nonneg_right _ hH0.le
    nlinarith
  have hwΔ := P2MGraphPHPAsymptoticParameters.width_bound n (width β n) hL1 hH1 hΔlog hwRange
  have hHready : β*A ≤ 2*δ*H := by
    have hh := (le_max_right 1 (β*A/(2*δ))).trans hHlarge
    have hc := (div_le_iff₀ (by positivity : (0 : ℝ)<2*δ)).mp hh
    dsimp only [H,L]
    nlinarith
  have hDen := P2MGraphSparsificationDenominatorNumerics.bound C β δ hC hβ hδ hδSlack n (php74Delta n)
    (width β n) hn hΔ hw hwΔ hL1 hH1 hDlog hDnear hwU hHready
  have hd : 0 < (width β n : ℝ)*php74Delta n*(C*(php74Delta n : ℝ)^2)^(width β n) := by
    have hwR : (0 : ℝ)<width β n := by exact_mod_cast (show 0 < width β n by omega)
    positivity
  have hDominates := P2MGraphSparsificationDominanceNumerics.bound a γ β _ ha hγ.le hd n hn hL1 hH1 hDen hGrowth
  have hSurvive := P2MGraphSparsificationSurvivalNumerics.bound γ β δ ξ hβ hξ hδ1 hgap n (php74Delta n)
    (width β n) hn hΔ hL1 hH0 hHL hDlog hwL
  have hExpQuarter : Real.exp (-ξ*L) ≤ (1/4 : ℝ) := by
    have hh := (le_max_right 1 (Real.log 4/ξ)).trans hLlarge
    have hl := (div_le_iff₀ hξ).mp hh
    have he : Real.exp (-Real.log 4)=(1/4 : ℝ) := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ)<4)]; norm_num
    rw [←he]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hErrorQuarter : 7/(n : ℝ)^3 ≤ (1/4 : ℝ) := by
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hn4 3
    norm_num at hh
    exact (div_le_iff₀ (by positivity : (0 : ℝ)<(n : ℝ)^3)).mpr (by linarith)
  exact ⟨by omega,hΔ,hΔn,hΔlog,hw,hwRange,by linarith [hSurvive.trans hExpQuarter],hDominates⟩

end SemAC02.Supplement.P2MGraphSparsificationAsymptoticParameters
end

section
-- Inlined Solutions.P2MBooleanAlgebra

open MvPolynomial AC02Frege
namespace AC02Frege.P2MBooleanAlgebra

theorem ml_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2) :
    ML (monomial s c) = monomial (sqfree s) c := by
  have h := (basisMonomials V (ZMod 2)).constr_basis (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) s
  have hc : monomial s c = c • monomial s (1 : ZMod 2) := by
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  change c • ((basisMonomials V (ZMod 2)).constr (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) (monomial s 1)) = _
  rw [show monomial s (1 : ZMod 2) = basisMonomials V (ZMod 2) s by rfl]
  rw [h]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem ml_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (ML p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial]
    intro t ht v
    have ht' : t = sqfree s := (Finset.mem_singleton.mp (support_monomial_subset ht))
    subst t
    simp [sqfree, Finsupp.mapRange_apply]
  | add p q hp hq =>
    rw [map_add]
    intro s hs v
    rcases Finset.mem_union.mp (support_add hs) with hs | hs
    · exact hp s hs v
    · exact hq s hs v


theorem sqfree_support {V : Type*} (s : V →₀ ℕ) : (sqfree s).support = s.support := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, sqfree, Finsupp.mapRange_apply]
  omega

theorem sqfree_eq_self {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) : sqfree s = s := by
  ext i
  simp only [sqfree, Finsupp.mapRange_apply, min_eq_left (hs i)]

theorem ml_of_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : ML p = p := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  conv_rhs => rw [p.as_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [sqfree_eq_self s (hp s hs)]

theorem ml_idempotent {V : Type*} (p : MvPolynomial V (ZMod 2)) : ML (ML p) = ML p :=
  ml_of_multilinear _ (ml_multilinear p)

theorem eval_ml {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (ML p) = eval x p := by
  classical
  have hpow (a : ZMod 2) (k : ℕ) : a ^ min k 1 = a ^ k := by
    fin_cases a
    · change (0 : ZMod 2) ^ min k 1 = (0 : ZMod 2) ^ k
      cases k <;> simp
    · change (1 : ZMod 2) ^ min k 1 = (1 : ZMod 2) ^ k
      simp
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial, eval_monomial, eval_monomial]
    congr 1
    simp only [Finsupp.prod, sqfree_support]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [sqfree, Finsupp.mapRange_apply] using hpow (x i) (s i)
  | add p q hp hq => simp only [map_add, hp, hq]

theorem multilinear_ext {V : Type} [Finite V]
    {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (h : ∀ x : V → ZMod 2, eval x p = eval x q) : p = q := by
  apply sub_eq_zero.mp
  apply MvPolynomial.eq_zero_of_eval_eq_zero V (ZMod 2) (p - q)
  · intro x; simp only [map_sub, h x, sub_self]
  · have hp' : p ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V p 1).mpr hp
    have hq' : q ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V q 1).mpr hq
    simpa only [ZMod.card, Nat.reduceSub] using (restrictDegree V (ZMod 2) 1).sub_mem hp' hq'

theorem ml_mul_left {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (ML p * q) = ML (p * q) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [eval_ml, map_mul]

theorem ml_mul_right {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (p * ML q) = ML (p * q) := by
  rw [mul_comm p (ML q), ml_mul_left, mul_comm]

theorem xMon_eq_monomial {V : Type*} (S : Finset V) :
    xMon S = monomial (Finsupp.indicator S (fun _ _ => 1)) (1 : ZMod 2) := by
  classical
  simpa only [xMon, pow_one] using (prod_X_pow (R := ZMod 2) (fun _ : V => 1) S)

theorem indicator_support {V : Type*} (S : Finset V) :
    (Finsupp.indicator S (fun _ _ => (1 : ℕ))).support = S := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, Finsupp.indicator_apply]
  split_ifs <;> simp_all

theorem xMon_multilinear {V : Type*} (S : Finset V) : IsMultilinear (xMon S) := by
  classical
  rw [xMon_eq_monomial]
  intro s hs i
  have heq := Finset.mem_singleton.mp (support_monomial_subset hs)
  subst s
  simp only [Finsupp.indicator_apply]
  split_ifs <;> omega

theorem xMon_eval {V : Type*} (S : Finset V) (x : V → ZMod 2) :
    eval x (xMon S) = ∏ i ∈ S, x i := by
  simp only [xMon, map_prod, eval_X]

theorem xMon_totalDegree {V : Type*} (S : Finset V) : (xMon S).totalDegree = S.card := by
  classical
  rw [xMon_eq_monomial, totalDegree_monomial _ (one_ne_zero : (1 : ZMod 2) ≠ 0)]
  simp only [Finsupp.sum, indicator_support]
  have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finsupp.indicator_apply, hi]
  rw [heq]
  simp

theorem xMon_linearIndependent {V : Type*} :
    LinearIndependent (ZMod 2) (fun S : Finset V => xMon S) := by
  classical
  have hinj : Function.Injective (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) := by
    intro S T h
    have := congrArg Finsupp.support h
    simpa only [indicator_support] using this
  have h := (basisMonomials V (ZMod 2)).linearIndependent.comp
    (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) hinj
  simpa only [Function.comp_def, coe_basisMonomials, xMon_eq_monomial] using h

end AC02Frege.P2MBooleanAlgebra
end

section
-- Inlined Solutions.P2MBooleanFieldPolynomials

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanFieldPolynomials

open MvPolynomial

lemma bool_power {F V : Type} [CommRing F] (x : V → Bool) (i : V) (a : ℕ) :
    (boolPt x i : F)^min a 1=(boolPt x i : F)^a := by
  cases h : x i <;> cases a <;> simp [boolPt,h]

theorem value_mlz {F V : Type} [CommRing F] (p : MvPolynomial V F) : polyFn (mlz p)=polyFn p := by
  classical
  funext x
  change eval (boolPt x) (mlz p)=eval (boolPt x) p
  rw [mlz,map_sum]
  conv_rhs => rw [p.as_sum,map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [eval_monomial,eval_monomial]
  congr 1
  simp only [Finsupp.prod,AC02Frege.P2MBooleanAlgebra.sqfree_support]
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [AC02Frege.sqfree,Finsupp.mapRange_apply] using bool_power (F:=F) x i (s i)

lemma monomial_value {F V : Type} [CommRing F] (s : V →₀ ℕ) (a : F) (x : V → Bool) :
    polyFn (monomial s a) x=a*∏ i∈s.support, (boolPt x i : F) := by
  classical
  rw [polyFn,eval_monomial]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have he : s i≠0 := Finsupp.mem_support_iff.mp hi
  cases h : x i <;> simp [boolPt,h,he]

end SemAC02.Supplement.P2MBooleanFieldPolynomials
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
-- Inlined Solutions.P2MPolynomialArithmeticCircuits

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPolynomialArithmeticCircuits

open MvPolynomial ACirc P2MArithmeticCircuitBasics

noncomputable def factors {F V : Type} (s : V →₀ ℕ) : List (ACirc F V) :=
  s.support.toList.flatMap (fun i => List.replicate (s i) (.var i))

noncomputable def monomialCircuit {F V : Type} (s : V →₀ ℕ) : ACirc F V := .prod (factors s)

noncomputable def polynomialCircuit {F V : Type} [CommRing F] (p : MvPolynomial V F) : ACirc F V :=
  .sum (p.support.toList.map (fun s => (coeff s p,monomialCircuit s)))

lemma factors_length {F V : Type} (s : V →₀ ℕ) : (factors (F:=F) s).length=s.sum (fun _ e => e) := by
  simp [factors,List.length_flatMap,Finsupp.sum,Finset.sum_toList]

lemma factors_leaves {F V : Type} (s : V →₀ ℕ) : ∀ c∈factors (F:=F) s, IsLeaf c := by
  intro c hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨_,rfl⟩ := List.mem_replicate.mp hc
  trivial

theorem monomial_layer {F V : Type} (s : V →₀ ℕ) (D : ℕ) (hs : s.sum (fun _ e => e) ≤ D) :
    IsMonGate (D : ℕ∞) (monomialCircuit (F:=F) s) := by
  constructor
  · rw [factors_length]
    exact_mod_cast hs
  · exact factors_leaves s

theorem monomial_poly {F V : Type} [CommRing F] (s : V →₀ ℕ) :
    (monomialCircuit (F:=F) s).toPoly=monomial s 1 := by
  classical
  rw [monomialCircuit,toPoly_prod,monomial_eq, C_1,one_mul]
  simp [factors,List.map_flatMap,List.flatMap_def,List.prod_flatten,Finsupp.prod,Finset.prod_map_toList,toPoly]

theorem polynomial_poly {F V : Type} [CommRing F] (p : MvPolynomial V F) :
    (polynomialCircuit p).toPoly=p := by
  rw [polynomialCircuit,toPoly_sum]
  simp only [List.map_map,Function.comp_def,monomial_poly,C_mul_monomial,mul_one]
  rw [Finset.sum_map_toList]
  exact support_sum_monomial_coeff p

theorem polynomial_layer {F V : Type} [CommRing F] (p : MvPolynomial V F) (D : ℕ)
    (hp : p.totalDegree ≤ D) : IsSumOf (IsMonGate (D : ℕ∞)) (polynomialCircuit p) := by
  intro z hz
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
  exact monomial_layer s D ((le_totalDegree (Finset.mem_toList.mp hs)).trans hp)

end SemAC02.Supplement.P2MPolynomialArithmeticCircuits
end

section
-- Inlined Solutions.P2MGraphSparsificationProjection

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MGraphSparsificationProjection

open MvPolynomial

abbrev CompleteEdge (m n : ℕ) := Edge (completeBip m n)

variable {m n D : ℕ}

def liftPoint (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D)
    (y : Fin n×Fin D → Bool) (e : CompleteEdge m n) : Bool :=
  if h : G.Adj e.1.1 e.1.2 then y (e.1.2,ι e.1.2 ⟨e.1.1,h⟩) else false

noncomputable def rho (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (e : CompleteEdge m n) :
    MvPolynomial (Fin n×Fin D) (ZMod 2) :=
  if h : G.Adj e.1.1 e.1.2 then X (e.1.2,ι e.1.2 ⟨e.1.1,h⟩) else 0

 theorem rho_degree (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (e : CompleteEdge m n) :
    (rho G ι e).totalDegree ≤ 1 := by
  unfold rho
  split_ifs <;> simp

 theorem rho_value (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D)
    (y : Fin n×Fin D → Bool) (e : CompleteEdge m n) :
    eval (boolPt y) (rho G ι e)=(boolPt (liftPoint G ι y) e : ZMod 2) := by
  by_cases he : G.Adj e.1.1 e.1.2 <;> simp [rho,liftPoint,he,boolPt]

 theorem pair_zero (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D)
    (y : Fin n×Fin D → Bool) (hy : nDivOmega n D y)
    (e e' : CompleteEdge m n) (hHole : e.1.2=e'.1.2) (hne : e≠e') :
    (boolPt (liftPoint G ι y) e : ZMod 2)=0 ∨ (boolPt (liftPoint G ι y) e' : ZMod 2)=0 := by
  by_cases he : G.Adj e.1.1 e.1.2
  · by_cases he' : G.Adj e'.1.1 e'.1.2
    · rcases e with ⟨⟨u,v⟩,huv⟩
      rcases e' with ⟨⟨u',v'⟩,huv'⟩
      dsimp only at hHole
      subst v'
      have hneU : u≠u' := by intro hh; subst u'; exact hne rfl
      by_cases hyj : y (v,ι v ⟨u,he⟩)=true
      · by_cases hyj' : y (v,ι v ⟨u',he'⟩)=true
        · have hh := hy v (ι v ⟨u,he⟩) (ι v ⟨u',he'⟩) hyj hyj'
          exact (hneU (congrArg Subtype.val ((ι v).injective hh))).elim
        · right
          simp [liftPoint,he',boolPt,hyj']
      · left
        simp [liftPoint,he,boolPt,hyj]
    · right
      simp [liftPoint,he',boolPt]
  · left
    simp [liftPoint,he,boolPt]

def Alive (G : PCNonBool.BipGraph (Fin m) (Fin n)) (s : CompleteEdge m n →₀ ℕ) : Prop :=
  (∀ e∈s.support, G.Adj e.1.1 e.1.2) ∧
    Set.InjOn (fun e : CompleteEdge m n => e.1.2) (s.support : Set (CompleteEdge m n))

 theorem killed (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D)
    (s : CompleteEdge m n →₀ ℕ) (hdead : ¬ Alive G s)
    (y : Fin n×Fin D → Bool) (hy : nDivOmega n D y) :
    (∏ e∈s.support, (boolPt (liftPoint G ι y) e : ZMod 2))=0 := by
  classical
  by_cases he : ∀ e∈s.support, G.Adj e.1.1 e.1.2
  · have hn : ¬ Set.InjOn (fun e : CompleteEdge m n => e.1.2) (s.support : Set (CompleteEdge m n)) :=
      fun hh => hdead ⟨he,hh⟩
    simp only [Set.InjOn,Finset.mem_coe,not_forall,_root_.not_imp] at hn
    obtain ⟨e,heS,e',heS',hHole,hne⟩ := hn
    rcases pair_zero G ι y hy e e' hHole hne with hz | hz
    · exact Finset.prod_eq_zero heS hz
    · exact Finset.prod_eq_zero heS' hz
  · push_neg at he
    obtain ⟨e,heS,heG⟩ := he
    exact Finset.prod_eq_zero heS (by simp [liftPoint,heG,boolPt])

noncomputable def project (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (w : ℕ)
    (p : MvPolynomial (CompleteEdge m n) (ZMod 2)) : MvPolynomial (Fin n×Fin D) (ZMod 2) :=
  ∑ s∈(mlz p).support.filter (fun s => s.support.card ≤ w),
    C (coeff s (mlz p))*∏ e∈s.support, rho G ι e

 theorem project_degree (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (w : ℕ)
    (p : MvPolynomial (CompleteEdge m n) (ZMod 2)) : (project G ι w p).totalDegree ≤ w := by
  apply totalDegree_finsetSum_le
  intro s hs
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C,zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _e∈s.support, 1 := Finset.sum_le_sum (fun e he => rho_degree G ι e)
    _ = s.support.card := by simp
    _ ≤ w := (Finset.mem_filter.mp hs).2

 theorem project_value (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (w : ℕ)
    (p : MvPolynomial (CompleteEdge m n) (ZMod 2))
    (hgood : ∀ s∈(mlz p).support, w < s.support.card → ¬ Alive G s)
    (y : Fin n×Fin D → Bool) (hy : nDivOmega n D y) :
    polyFn (project G ι w p) y=polyFn p (liftPoint G ι y) := by
  classical
  rw [←P2MBooleanFieldPolynomials.value_mlz p]
  change eval (boolPt y) (project G ι w p)=polyFn (mlz p) (liftPoint G ι y)
  rw [project,map_sum]
  conv_rhs => rw [(mlz p).as_sum]
  simp only [polyFn,map_sum,P2MBooleanFieldPolynomials.monomial_value]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show eval (boolPt (liftPoint G ι y)) (monomial s (coeff s (mlz p)))=
      coeff s (mlz p)*∏ e∈s.support, (boolPt (liftPoint G ι y) e : ZMod 2) from
    P2MBooleanFieldPolynomials.monomial_value s (coeff s (mlz p)) (liftPoint G ι y)]
  by_cases hsmall : s.support.card ≤ w
  · simp only [if_pos hsmall,map_mul,eval_C,map_prod,rho_value]
  · simp only [if_neg hsmall]
    rw [killed G ι s (hgood s hs (by omega)) y hy,mul_zero]

end SemAC02.Supplement.P2MGraphSparsificationProjection
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
-- Inlined Solutions.P2MBernoulliAlgebra

open Finset

namespace SemAC02.P2MBernoulliAlgebra

noncomputable def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

noncomputable def weight {I : Type*} [Fintype I] (p : ℝ) (x : I → Bool) : ℝ :=
  ∏ i, bitWeight p (x i)

theorem bitWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (b : Bool) : 0 ≤ bitWeight p b := by
  cases b
  · simpa [bitWeight] using sub_nonneg.mpr hp'
  · simpa [bitWeight] using hp

theorem weight_nonneg {I : Type*} [Fintype I] {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (x : I → Bool) :
    0 ≤ weight p x := prod_nonneg (fun _ _ => bitWeight_nonneg hp hp' _)

@[simp] theorem bitWeight_sum (p : ℝ) : ∑ b : Bool, bitWeight p b = 1 := by
  simp [bitWeight]

@[simp] theorem weight_sum (I : Type*) [Fintype I] [DecidableEq I] (p : ℝ) : ∑ x : I → Bool, weight p x = 1 := by
  simp only [weight]
  rw [← Fintype.prod_sum]
  simp only [bitWeight_sum,prod_const_one]

theorem bernProb_eq_weight (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p E = ∑ x, if E x then weight p x else 0 := rfl

@[simp] theorem prob_true (p : ℝ) (m : ℕ) : bernProb p (fun _ : Fin m → Bool => true) = 1 := by
  simp [bernProb_eq_weight]

@[simp] theorem prob_false (p : ℝ) (m : ℕ) : bernProb p (fun _ : Fin m → Bool => false) = 0 := by
  simp [bernProb_eq_weight]

theorem prob_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    0 ≤ bernProb p E := by
  rw [bernProb_eq_weight]
  apply sum_nonneg
  intro x _
  split_ifs
  · exact weight_nonneg hp hp' x
  · exact le_rfl

theorem prob_le_one {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p E ≤ 1 := by
  rw [bernProb_eq_weight,← weight_sum (Fin m) p]
  apply sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact weight_nonneg hp hp' x

theorem prob_add_compl (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p E + bernProb p (fun x => !E x) = 1 := by
  rw [bernProb_eq_weight,bernProb_eq_weight,← sum_add_distrib,← weight_sum (Fin m) p]
  apply sum_congr rfl
  intro x _
  cases he : E x <;> simp [he]

theorem prob_compl (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p (fun x => !E x) = 1-bernProb p E := by
  linarith [prob_add_compl p E]

def complementEquiv (I : Type*) : (I → Bool) ≃ (I → Bool) where
  toFun x i := !x i
  invFun x i := !x i
  left_inv x := by funext i; simp only [Bool.not_not]
  right_inv x := by funext i; simp only [Bool.not_not]

theorem bitWeight_compl (p : ℝ) (b : Bool) : bitWeight p (!b) = bitWeight (1-p) b := by
  cases b <;> simp [bitWeight]

theorem weight_compl {I : Type*} [Fintype I] (p : ℝ) (x : I → Bool) :
    weight p (complementEquiv I x) = weight (1-p) x := by
  unfold weight
  apply prod_congr rfl
  intro i _
  exact bitWeight_compl p (x i)

theorem prob_complement_inputs (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p (fun x => E (fun i => !x i)) = bernProb (1-p) E := by
  rw [bernProb_eq_weight,bernProb_eq_weight]
  have he := Equiv.sum_comp (complementEquiv (Fin m))
    (fun x => if E (fun i => !x i) then weight p x else 0)
  rw [← he]
  apply sum_congr rfl
  intro x _
  simp only [complementEquiv,Equiv.coe_fn_mk,Bool.not_not]
  exact congrArg (fun w : ℝ => if E x then w else 0) (weight_compl p x)

end SemAC02.P2MBernoulliAlgebra
end

section
-- Inlined Solutions.P2MBernoulliProduct

set_option maxHeartbeats 1000000

open Finset SemAC02.P2MBernoulliAlgebra

namespace SemAC02.P2MBernoulliProduct

/-- The same finite product probability on an arbitrary finite coordinate type. -/
noncomputable def prob {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ) (E : (I → Bool) → Bool) : ℝ :=
  ∑ x, if E x then weight p x else 0

theorem prob_complement {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ) (E : (I → Bool) → Bool) :
    prob p (fun x => !E x) = 1-prob p E := by
  classical
  have h : prob p E + prob p (fun x => !E x) = 1 := by
    rw [prob,prob,← sum_add_distrib,← weight_sum I p]
    apply sum_congr rfl
    intro x _
    cases he : E x <;> simp [he]
  linarith

theorem prob_all_coordinates {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ) :
    prob p (fun x : I → Bool => decide (∀ i, x i = true)) = p ^ Fintype.card I := by
  classical
  unfold prob
  have he : (fun x : I → Bool => if decide (∀ i, x i = true) then weight p x else 0) =
      (fun x => if x = (fun _ => true) then weight p x else 0) := by
    funext x
    congr 1
    simp only [decide_eq_true_eq,funext_iff]
  rw [he]
  simp [weight,bitWeight]

theorem prob_fin {m : ℕ} (p : ℝ) (E : (Fin m → Bool) → Bool) :
    prob p E = bernProb p E := rfl

def assignmentEquiv {I J : Type*} (e : I ≃ J) : (I → Bool) ≃ (J → Bool) where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp

theorem weight_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : ℝ) (x : I → Bool) : weight p (assignmentEquiv e x) = weight p x := by
  unfold weight
  exact Fintype.prod_equiv e.symm _ _ (fun j => rfl)

theorem prob_equiv {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (p : ℝ) (E : (I → Bool) → Bool) :
    prob p (fun y : J → Bool => E (fun i => y (e i))) = prob p E := by
  classical
  unfold prob
  rw [← Equiv.sum_comp (assignmentEquiv e)]
  apply sum_congr rfl
  intro x _
  have he : (fun i => assignmentEquiv e x (e i)) = x := by funext i; simp [assignmentEquiv]
  change (if E (fun i => assignmentEquiv e x (e i)) then weight p (assignmentEquiv e x) else 0) = _
  rw [he,weight_equiv]

theorem weight_product {I J : Type*} [Fintype I] [Fintype J]
    (p : ℝ) (x : I × J → Bool) :
    weight p x = ∏ i, weight p (fun j => x (i,j)) := by
  simp only [weight,Fintype.prod_prod_type]

theorem indicator_all {I : Type*} [Fintype I] (E : I → Bool) (w : I → ℝ) :
    (if (decide (∀ i, E i = true)) then ∏ i, w i else 0) =
      ∏ i, if E i then w i else 0 := by
  classical
  by_cases h : ∀ i, E i = true
  · simp [h]
  · have hz : ∃ i, E i = false := by simpa only [not_forall,Bool.not_eq_true] using h
    obtain ⟨i,hi⟩ := hz
    rw [if_neg (by simpa using h)]
    symm
    exact prod_eq_zero (mem_univ i) (by simp [hi])

/-- Disjoint blocks have independent acceptance events under product bias. -/
theorem prob_all_blocks {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (p : ℝ) (E : I → (J → Bool) → Bool) :
    prob p (fun x : I × J → Bool => decide (∀ i, E i (fun j => x (i,j)) = true)) =
      ∏ i, prob p (E i) := by
  classical
  unfold prob
  simp_rw [weight_product,indicator_all]
  rw [Fintype.sum_equiv (Equiv.curry I J Bool)
    (fun x : I × J → Bool => ∏ i, if E i (fun j => x (i,j)) then weight p (fun j => x (i,j)) else 0)
    (fun x : I → J → Bool => ∏ i, if E i (x i) then weight p (x i) else 0) (fun _ => rfl)]
  exact (Fintype.prod_sum (fun i : I => fun x : J → Bool => if E i x then weight p x else 0)).symm

theorem prob_all_copies {t m : ℕ} (p : ℝ) (E : (Fin m → Bool) → Bool) :
    prob p (fun x : Fin t × Fin m → Bool => decide (∀ i, E (fun j => x (i,j)) = true)) =
      bernProb p E ^ t := by
  convert (prob_all_blocks p (fun _ : Fin t => E)) using 1
  · congr 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp
  · simp only [prob_fin,prod_const,card_univ,Fintype.card_fin]

end SemAC02.P2MBernoulliProduct
end

section
-- Inlined Solutions.P2MFiniteProductPushforward

open Finset

namespace ProofComplexity.P2MFiniteProductPushforward

theorem prod_fiber_indicator {I A B : Type*} [Fintype I] [DecidableEq I] [DecidableEq B] (g : A → B)
    (w : I → A → ℝ) (x : I → A) (y : I → B) :
    (if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0) =
      ∏ i, if g (x i) = y i then w i (x i) else 0 := by
  classical
  by_cases he : (fun i => g (x i)) = y
  · rw [if_pos he]
    apply prod_congr rfl
    intro i _
    rw [if_pos (congrFun he i)]
  · rw [if_neg he]
    obtain ⟨i,hi⟩ : ∃ i, g (x i) ≠ y i := by
      by_contra! h
      exact he (funext h)
    symm
    exact prod_eq_zero (mem_univ i) (if_neg hi)

theorem fiber_weight {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq B] (g : A → B)
    (w : I → A → ℝ) (y : I → B) :
    (∑ x : I → A, if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0) =
      ∏ i, ∑ a : A, if g a = y i then w i a else 0 := by
  classical
  simp_rw [prod_fiber_indicator]
  exact (Fintype.prod_sum (fun i : I => fun a : A => if g a = y i then w i a else 0)).symm

/-- Independent finite coordinates remain independent under a coordinatewise map. -/
theorem sum_pushforward {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B] [DecidableEq B]
    (g : A → B) (w : I → A → ℝ) (F : (I → B) → ℝ) :
    (∑ x : I → A, (∏ i, w i (x i))*F (fun i => g (x i))) =
      ∑ y : I → B, (∏ i, ∑ a : A, if g a = y i then w i a else 0)*F y := by
  classical
  calc
    _ = ∑ x : I → A, ∑ y : I → B,
        (if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0)*F y := by
      apply sum_congr rfl
      intro x _
      simp only [ite_mul,zero_mul]
      simp
    _ = ∑ y : I → B, ∑ x : I → A,
        (if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0)*F y := sum_comm
    _ = ∑ y : I → B,
        (∑ x : I → A, if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0)*F y := by
      simp only [sum_mul]
    _ = _ := by simp only [fiber_weight]

end ProofComplexity.P2MFiniteProductPushforward
end

section
-- Inlined Solutions.P2MBernoulliProductBounds

set_option maxHeartbeats 2000000

namespace SemAC02.P2MBernoulliProductBounds

open Finset P2MBernoulliAlgebra P2MBernoulliProduct

variable {I : Type} [Fintype I] [DecidableEq I]

 theorem nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (E : (I → Bool) → Bool) : 0 ≤ prob p E := by
  unfold prob
  apply sum_nonneg
  intro x hx
  split_ifs
  · exact weight_nonneg hp hp1 x
  · rfl

 theorem mono (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (E F : (I → Bool) → Bool)
    (h : ∀ x, E x=true → F x=true) : prob p E ≤ prob p F := by
  unfold prob
  apply sum_le_sum
  intro x hx
  cases he : E x
  · simp only [he,Bool.false_eq_true,↓reduceIte]
    split_ifs
    · exact weight_nonneg hp hp1 x
    · rfl
  · simp only [he,h x he,↓reduceIte,le_refl]

 theorem le_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (E : (I → Bool) → Bool) : prob p E ≤ 1 := by
  have hh := mono p hp hp1 E (fun _ => true) (fun _ _ => rfl)
  simpa only [prob,↓reduceIte,weight_sum] using hh

 theorem union_bound {J : Type} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset J)
    (E : (I → Bool) → Bool) (F : J → (I → Bool) → Bool)
    (h : ∀ x, E x=true → ∃ j∈S, F j x=true) : prob p E ≤ ∑ j∈S, prob p (F j) := by
  classical
  unfold prob
  rw [sum_comm]
  apply sum_le_sum
  intro x hx
  cases he : E x
  · simp only [he,Bool.false_eq_true,↓reduceIte]
    apply sum_nonneg
    intro j hj
    split_ifs
    · exact weight_nonneg hp hp1 x
    · rfl
  · obtain ⟨j,hj,hF⟩ := h x he
    simp only [he,↓reduceIte]
    apply le_trans _ (single_le_sum (fun k hk => ?_) hj)
    · simpa only [hF,↓reduceIte] using (le_refl (weight p x))
    · split_ifs
      · exact weight_nonneg hp hp1 x
      · rfl

 theorem positive_exists (p : ℝ) (E : (I → Bool) → Bool) (h : 0 < prob p E) : ∃ x, E x=true := by
  classical
  by_contra! hh
  have hz : prob p E=0 := by unfold prob; simp [hh]
  linarith

 theorem independent (p : ℝ) (E : I → Bool → Bool) :
    prob p (fun x : I → Bool => decide (∀ i, E i (x i)=true))=
      ∏ i, ∑ b : Bool, if E i b then bitWeight p b else 0 := by
  classical
  unfold prob
  simp_rw [weight,indicator_all]
  exact (Fintype.prod_sum (fun i : I => fun b : Bool => if E i b then bitWeight p b else 0)).symm

 theorem all_on_subset (p : ℝ) (S : Finset I) :
    prob p (fun x : I → Bool => decide (∀ i∈S, x i=true))=p^S.card := by
  classical
  have hh := independent p (fun i b => decide (i∈S → b=true))
  have he (i : I) : (∑ b : Bool, if decide (i∈S → b=true) then bitWeight p b else 0)=if i∈S then p else 1 := by
    by_cases hi : i∈S <;> simp [hi,bitWeight]
  simp only [he] at hh
  rw [←prod_filter] at hh
  have hf : (univ : Finset I).filter (· ∈ S)=S := by ext i; simp
  rw [hf,prod_const] at hh
  have hEvent : (fun x : I → Bool => decide (∀ i∈S, x i=true))=
      (fun x => decide (∀ i, decide (i∈S → x i=true)=true)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
  rw [hEvent]
  exact hh

 theorem transform_blocks {J : Type} [Fintype J] [DecidableEq J]
    (p : ℝ) (g : (J → Bool) → Bool) (E : (I → Bool) → Bool) :
    prob p (fun x : I×J → Bool => E (fun i => g (fun j => x (i,j))))=
      prob (prob p g) E := by
  classical
  let q := prob p g
  have hf (b : Bool) : (∑ z : J → Bool, if g z=b then weight p z else 0)=bitWeight q b := by
    cases b
    · have hh := prob_complement p g
      simpa [prob,bitWeight,q] using hh
    · simp [bitWeight,q,prob]
  have hh := ProofComplexity.P2MFiniteProductPushforward.sum_pushforward g (fun _ : I => weight p)
    (fun x : I → Bool => if E x then (1 : ℝ) else 0)
  have he := Fintype.sum_equiv (Equiv.curry I J Bool)
    (fun x : I×J → Bool => weight p x*(if E (fun i => g (fun j => x (i,j))) then (1 : ℝ) else 0))
    (fun x : I → J → Bool => (∏ i,weight p (x i))*(if E (fun i => g (x i)) then (1 : ℝ) else 0))
    (fun x => by rw [weight_product]; rfl)
  change (∑ x : I×J → Bool, if E (fun i => g (fun j => x (i,j))) then weight p x else 0)=
    ∑ x : I → Bool, if E x then weight q x else 0
  simp only [mul_ite,mul_one,mul_zero] at he hh
  rw [he,hh]
  simp_rw [hf]
  rfl

end SemAC02.P2MBernoulliProductBounds
end

section
-- Inlined Solutions.P2MBernoulliPatternProbability

set_option maxHeartbeats 2000000

namespace SemAC02.P2MBernoulliPatternProbability

open Finset P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds

variable {I : Type} [Fintype I] [DecidableEq I]

 theorem pattern (p : ℝ) (S : Finset I) (β : I → Bool) :
    prob p (fun x : I → Bool => decide (∀ i∈S, x i=β i))=∏ i∈S, bitWeight p (β i) := by
  classical
  have hh := independent p (fun i b => decide (i∈S → b=β i))
  have he (i : I) : (∑ b : Bool, if decide (i∈S → b=β i) then bitWeight p b else 0)=
      if i∈S then bitWeight p (β i) else 1 := by
    by_cases hi : i∈S <;> cases hb : β i <;> simp [hi,hb,bitWeight]
  simp only [he] at hh
  rw [←prod_filter] at hh
  have hf : (univ : Finset I).filter (· ∈ S)=S := by ext i; simp
  rw [hf] at hh
  have hEvent : (fun x : I → Bool => decide (∀ i∈S, x i=β i))=
      (fun x => decide (∀ i, decide (i∈S → x i=β i)=true)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
  rw [hEvent]
  exact hh

 theorem disjoint_union {J : Type} (p : ℝ) (S : Finset J)
    (E : (I → Bool) → Bool) (F : J → (I → Bool) → Bool)
    (hcover : ∀ x, E x=true ↔ ∃ j∈S, F j x=true)
    (hdisj : ∀ x, ∀ j∈S, ∀ k∈S, F j x=true → F k x=true → j=k) :
    prob p E=∑ j∈S, prob p (F j) := by
  classical
  unfold prob
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  by_cases he : E x=true
  · obtain ⟨j,hj,hF⟩ := (hcover x).mp he
    rw [if_pos he]
    symm
    rw [sum_eq_single j]
    · simp [hF]
    · intro k hk hkj
      have hn : F k x≠true := fun hf => hkj (hdisj x k hk j hj hf hF)
      simp [hn]
    · exact fun hn => (hn hj).elim
  · rw [if_neg he]
    symm
    apply sum_eq_zero
    intro j hj
    have hn : F j x≠true := fun hf => he ((hcover x).mpr ⟨j,hj,hf⟩)
    simp [hn]

 theorem one_pattern (p : ℝ) (S : Finset I) (j : I) (hj : j∈S) :
    prob p (fun x : I → Bool => decide (∀ i∈S, x i=decide (i=j)))=
      p*(1-p)^(S.card-1) := by
  classical
  rw [pattern,←mul_prod_erase S (fun i => bitWeight p (decide (i=j))) hj]
  have he : (∏ i∈S.erase j, bitWeight p (decide (i=j)))=(1-p)^(S.card-1) := by
    have hh : (∏ i∈S.erase j, bitWeight p (decide (i=j)))=∏ _i∈S.erase j, (1-p) := by
      apply prod_congr rfl
      intro i hi
      simp [bitWeight,(mem_erase.mp hi).1]
    rw [hh,prod_const,card_erase_of_mem hj]
  rw [he]
  simp [bitWeight]

 theorem exactly_one (p : ℝ) (S : Finset I) :
    prob p (fun x : I → Bool => decide ((S.filter (fun i => x i=true)).card=1))=
      (S.card : ℝ)*p*(1-p)^(S.card-1) := by
  classical
  let F := fun j (x : I → Bool) => decide (∀ i∈S, x i=decide (i=j))
  have hcover : ∀ x : I → Bool,
      decide ((S.filter (fun i => x i=true)).card=1)=true ↔ ∃ j∈S, F j x=true := by
    intro x
    simp only [decide_eq_true_eq]
    constructor
    · intro hc
      obtain ⟨j,hj⟩ := card_eq_one.mp hc
      have hjFilt : j∈S.filter (fun i => x i=true) := by rw [hj]; simp
      have hjS : j∈S := (mem_filter.mp hjFilt).1
      refine ⟨j,hjS,?_⟩
      apply decide_eq_true
      intro i hi
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro hxi
        have hm : i∈S.filter (fun a => x a=true) := mem_filter.mpr ⟨hi,hxi⟩
        rw [hj] at hm
        exact mem_singleton.mp hm
      · intro hij
        subst i
        exact (mem_filter.mp hjFilt).2
    · rintro ⟨j,hj,hF⟩
      have hF' : ∀ i∈S, x i=decide (i=j) := of_decide_eq_true hF
      have he : S.filter (fun i => x i=true)={j} := by
        ext i
        simp only [mem_filter,mem_singleton]
        constructor
        · rintro ⟨hi,hxi⟩
          have hh := hF' i hi
          rw [hxi] at hh
          exact of_decide_eq_true hh.symm
        · intro hij
          subst i
          exact ⟨hj,by simpa using hF' j hj⟩
      rw [he,card_singleton]
  have hdisj : ∀ x, ∀ j∈S, ∀ k∈S, F j x=true → F k x=true → j=k := by
    intro x j hj k hk hFj hFk
    have hJ := of_decide_eq_true hFj j hj
    have hK := of_decide_eq_true hFk j hj
    have hxj : x j=true := by simpa using hJ
    rw [hxj] at hK
    exact of_decide_eq_true hK.symm
  rw [disjoint_union p S _ F hcover hdisj]
  have he (j : I) (hj : j∈S) : prob p (F j)=p*(1-p)^(S.card-1) := one_pattern p S j hj
  rw [sum_congr rfl he,sum_const,nsmul_eq_mul]
  ring

end SemAC02.P2MBernoulliPatternProbability
end

section
-- Inlined Solutions.P2MBernoulliTail

set_option maxHeartbeats 2000000

open Finset SemAC02.P2MBernoulliAlgebra

namespace SemAC02.P2MBernoulliTail

def bitValue (b : Bool) : ℝ := if b then 1 else 0

theorem weight_eq_sum {m : ℕ} (x : Fin m → Bool) :
    (hammingWeight x : ℝ) = ∑ i, bitValue (x i) := by
  simp [hammingWeight,bitValue]

theorem exp_weight {m : ℕ} (θ : ℝ) (x : Fin m → Bool) :
    Real.exp (θ*(hammingWeight x : ℝ)) = ∏ i, Real.exp (θ*bitValue (x i)) := by
  rw [weight_eq_sum,mul_sum,Real.exp_sum]

theorem moment_formula {m : ℕ} (p θ : ℝ) :
    (∑ x : Fin m → Bool, weight p x*Real.exp (θ*(hammingWeight x : ℝ))) =
      (1-p+p*Real.exp θ)^m := by
  simp_rw [exp_weight,weight,← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun _ : Fin m => fun b : Bool => bitWeight p b*Real.exp (θ*bitValue b))]
  simp [bitWeight,bitValue,add_comm]

theorem moment_markov {m : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ)
    (t : ℝ) (E : (Fin m → Bool) → Bool)
    (hE : ∀ x, E x = true → t ≤ (hammingWeight x : ℝ)) :
    bernProb p E ≤ Real.exp (-θ*t)*(1-p+p*Real.exp θ)^m := by
  have hs : bernProb p E*Real.exp (θ*t) ≤ (1-p+p*Real.exp θ)^m := by
    rw [bernProb_eq_weight,sum_mul,← moment_formula]
    apply sum_le_sum
    intro x _
    cases he : E x
    · simp only [he,Bool.false_eq_true,↓reduceIte,zero_mul]
      exact mul_nonneg (weight_nonneg hp hp' x) (Real.exp_pos _).le
    · simp only [he,↓reduceIte]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hE x he) hθ)) (weight_nonneg hp hp' x)
  calc
    _ = (bernProb p E*Real.exp (θ*t))*Real.exp (-θ*t) := by
      rw [mul_assoc,← Real.exp_add,show θ*t+(-θ*t) = 0 by ring,Real.exp_zero,mul_one]
    _ ≤ (1-p+p*Real.exp θ)^m*Real.exp (-θ*t) :=
      mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem exp_quadratic_bound {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/2) :
    Real.exp θ ≤ 1+θ+2*θ^2 := by
  apply (Real.exp_bound_div_one_sub_of_interval hθ (by linarith : θ < 1)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-θ)).mpr
  nlinarith [mul_nonneg (sq_nonneg θ) (by linarith : 0 ≤ 1-2*θ)]

theorem moment_bound {m : ℕ} {p θ : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/2) :
    (1-p+p*Real.exp θ)^m ≤ Real.exp ((m : ℝ)*(p*θ+2*p*θ^2)) := by
  have hb : 1-p+p*Real.exp θ ≤ Real.exp (p*θ+2*p*θ^2) := by
    have he := mul_le_mul_of_nonneg_left (exp_quadratic_bound hθ hθ') hp
    linarith [Real.add_one_le_exp (p*θ+2*p*θ^2)]
  calc
    _ ≤ Real.exp (p*θ+2*p*θ^2)^m := pow_le_pow_left₀
      (add_nonneg (sub_nonneg.mpr hp') (mul_nonneg hp (Real.exp_pos _).le)) hb m
    _ = _ := (Real.exp_nat_mul _ _).symm

/-- A finite-sum Chernoff estimate; its constant suffices for the covering-gadget construction. -/
theorem upper_tail {m : ℕ} {p δ : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1/2)
    (hδ : 0 < δ) (hδ' : δ ≤ 1) (E : (Fin m → Bool) → Bool)
    (hE : ∀ x, E x = true → (p+δ)*(m : ℝ) ≤ (hammingWeight x : ℝ)) :
    bernProb p E ≤ Real.exp (-((m : ℝ)*δ^2/4)) := by
  let θ := δ/2
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ' : θ ≤ 1/2 := by dsimp [θ]; linarith
  calc
    _ ≤ Real.exp (-θ*((p+δ)*(m : ℝ)))*(1-p+p*Real.exp θ)^m :=
      moment_markov hp (by linarith : p ≤ 1) hθ _ E hE
    _ ≤ Real.exp (-θ*((p+δ)*(m : ℝ)))*Real.exp ((m : ℝ)*(p*θ+2*p*θ^2)) :=
      mul_le_mul_of_nonneg_left (moment_bound hp (by linarith : p ≤ 1) hθ hθ') (Real.exp_pos _).le
    _ = Real.exp ((m : ℝ)*(2*p*θ^2-θ*δ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hsmall : 2*p*θ^2-θ*δ ≤ -δ^2/4 := by
        dsimp [θ]
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1-2*p) (sq_nonneg δ)]
      have h := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg m)
      nlinarith

theorem covering_tail {m : ℕ} {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/2) :
    bernProb (1/2-ε)
      (fun x : Fin m → Bool => decide ((1/2-3*ε/4)*(m : ℝ) < (hammingWeight x : ℝ))) ≤
      Real.exp (-((m : ℝ)*ε^2/64)) := by
  have h := upper_tail (p := 1/2-ε) (δ := ε/4) (by linarith) (by linarith)
    (by positivity) (by linarith) (fun x : Fin m → Bool =>
      decide ((1/2-3*ε/4)*(m : ℝ) < (hammingWeight x : ℝ))) (by
        intro x hx
        have ht := of_decide_eq_true hx
        nlinarith)
  convert h using 1 <;> congr 1 <;> ring

end SemAC02.P2MBernoulliTail
end

section
-- Inlined Solutions.P2MBernoulliMultiplicativeTail

set_option maxHeartbeats 2000000

namespace SemAC02.P2MBernoulliMultiplicativeTail

open Finset P2MBernoulliAlgebra P2MBernoulliTail

 theorem poisson_moment {m : ℕ} (p θ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1-p+p*Real.exp θ)^m ≤ Real.exp ((m : ℝ)*p*(Real.exp θ-1)) := by
  have hb : 1-p+p*Real.exp θ ≤ Real.exp (p*(Real.exp θ-1)) := by
    have hh := Real.add_one_le_exp (p*(Real.exp θ-1))
    nlinarith
  have hbase : 0 ≤ 1-p+p*Real.exp θ := by positivity
  calc
    _ ≤ Real.exp (p*(Real.exp θ-1))^m := pow_le_pow_left₀ hbase hb m
    _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring

 theorem upper_twice {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (E : (Fin m → Bool) → Bool) (hE : ∀ x, E x=true → 2*p*m ≤ (hammingWeight x : ℝ)) :
    bernProb p E ≤ Real.exp (-((m : ℝ)*p)/3) := by
  have hθ : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := (moment_markov hp hp1 hθ (2*p*m) E hE).trans
    (mul_le_mul_of_nonneg_left (poisson_moment p (Real.log 2) hp hp1) (Real.exp_pos _).le)
  rw [←Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ)<2)] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hl : (2/3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm : (0 : ℝ) ≤ (m : ℝ)*p := by positivity
  nlinarith [mul_nonneg hm (sub_nonneg.mpr hl)]

 theorem moment_markov_lower {m : ℕ} (p θ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hθ : θ ≤ 0)
    (t : ℝ) (E : (Fin m → Bool) → Bool) (hE : ∀ x, E x=true → (hammingWeight x : ℝ) ≤ t) :
    bernProb p E ≤ Real.exp (-θ*t)*(1-p+p*Real.exp θ)^m := by
  have hs : bernProb p E*Real.exp (θ*t) ≤ (1-p+p*Real.exp θ)^m := by
    rw [bernProb_eq_weight,sum_mul,←moment_formula]
    apply sum_le_sum
    intro x hx
    cases he : E x
    · simp only [he,Bool.false_eq_true,↓reduceIte,zero_mul]
      exact mul_nonneg (weight_nonneg hp hp1 x) (Real.exp_pos _).le
    · simp only [he,↓reduceIte]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (hE x he) hθ)) (weight_nonneg hp hp1 x)
  calc
    _ = (bernProb p E*Real.exp (θ*t))*Real.exp (-θ*t) := by
      rw [mul_assoc,←Real.exp_add,show θ*t+(-θ*t)=0 by ring,Real.exp_zero,mul_one]
    _ ≤ (1-p+p*Real.exp θ)^m*Real.exp (-θ*t) := mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
    _ = _ := mul_comm _ _

 theorem lower_third {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (E : (Fin m → Bool) → Bool) (hE : ∀ x, E x=true → (hammingWeight x : ℝ) ≤ (m : ℝ)*p/3) :
    bernProb p E ≤ Real.exp (-2*((m : ℝ)*p)/9) := by
  have hθ : -Real.log 2 ≤ 0 := neg_nonpos.mpr (Real.log_nonneg (by norm_num))
  have hh := (moment_markov_lower p (-Real.log 2) hp hp1 hθ ((m : ℝ)*p/3) E hE).trans
    (mul_le_mul_of_nonneg_left (poisson_moment p (-Real.log 2) hp hp1) (Real.exp_pos _).le)
  have hexp : Real.exp (-Real.log 2)=(1/2 : ℝ) := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ)<2)]; norm_num
  rw [←Real.exp_add,hexp] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hl : Real.log 2 ≤ (5/6 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hm : (0 : ℝ) ≤ (m : ℝ)*p := by positivity
  nlinarith [mul_nonneg hm (sub_nonneg.mpr hl)]

end SemAC02.P2MBernoulliMultiplicativeTail
end

section
-- Inlined Solutions.P2MRandomGraphFixedBoundary

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomGraphFixedBoundary

open Finset P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds

noncomputable def graph (n : ℕ) (x : Fin n×Fin (2*n) → Bool) :
    PCNonBool.BipGraph (Fin (2*n)) (Fin n) where
  Adj u v := x (v,u)=true

noncomputable def oneNeighbor {I : Type} [DecidableEq I] (S : Finset I) (x : I → Bool) : Bool :=
  decide ((S.filter (fun i => x i=true)).card=1)

 theorem one_neighbor_lower {I : Type} [Fintype I] [DecidableEq I]
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset I) (hSmall : (S.card : ℝ)*p ≤ 1/4) :
    3/4*(S.card : ℝ)*p ≤ prob p (oneNeighbor S) := by
  rw [show oneNeighbor S=(fun x : I → Bool => decide ((S.filter (fun i => x i=true)).card=1)) from rfl,
    P2MBernoulliPatternProbability.exactly_one]
  have hh := one_add_mul_le_pow (a := -p) (by linarith : -2 ≤ -p) (S.card-1)
  have hc : ((S.card-1 : ℕ) : ℝ) ≤ S.card := by exact_mod_cast Nat.sub_le S.card 1
  have hpow : (3/4 : ℝ) ≤ (1-p)^(S.card-1) := by
    have hh' : 1-((S.card-1 : ℕ) : ℝ)*p ≤ (1-p)^(S.card-1) := by simpa only [mul_neg,←sub_eq_add_neg] using hh
    nlinarith [mul_le_mul_of_nonneg_right hc hp]
  have hmult := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (S.card : ℝ)*p by positivity)
  nlinarith

 theorem boundary_card (n : ℕ) (S : Finset (Fin (2*n))) (x : Fin n×Fin (2*n) → Bool) :
    (PCNonBool.boundaryOn (graph n x) univ S).card=
      hammingWeight (fun v : Fin n => oneNeighbor S (fun u => x (v,u))) := by
  unfold PCNonBool.boundaryOn hammingWeight
  congr 1
  apply filter_congr
  intro v hv
  simp only [graph,oneNeighbor,decide_eq_true_eq]
  apply Iff.of_eq
  congr 1

 theorem failure_bound (n Δ : ℕ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ) (hΔn : Δ ≤ n)
    (S : Finset (Fin (2*n))) (hS : (S.card : ℝ)*(Δ : ℝ)/n ≤ 1/4) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool =>
      decide (((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(S.card : ℝ)*Δ/4)) ≤
        Real.exp (-((S.card : ℝ)*Δ)/6) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  let p := (Δ : ℝ)/n
  let q := prob p (oneNeighbor S)
  let E := fun z : Fin n → Bool => decide ((hammingWeight z : ℝ)<(S.card : ℝ)*Δ/4)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hΔn)
  have hq : 0 ≤ q := nonneg p hp hp1 _
  have hq1 : q ≤ 1 := le_one p hp hp1 _
  have hSmall : (S.card : ℝ)*p ≤ 1/4 := by simpa only [p,mul_div_assoc] using hS
  have hqL : 3/4*(S.card : ℝ)*p ≤ q := one_neighbor_lower p hp hp1 S hSmall
  have hMu : 3/4*(S.card : ℝ)*Δ ≤ (n : ℝ)*q := by
    have hh := mul_le_mul_of_nonneg_left hqL hnR.le
    have he : (n : ℝ)*(3/4*(S.card : ℝ)*p)=3/4*(S.card : ℝ)*Δ := by dsimp [p]; field_simp
    rwa [he] at hh
  have he : prob p (fun x : Fin n×Fin (2*n) → Bool =>
      decide (((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(S.card : ℝ)*Δ/4))=bernProb q E := by
    have hh := transform_blocks p (oneNeighbor S) E
    convert hh using 1
    congr 1
    funext x
    rw [boundary_card]
    rfl
  rw [he]
  have hh := P2MBernoulliMultiplicativeTail.lower_third q hq hq1 E (by
    intro z hz
    have ht := of_decide_eq_true hz
    linarith)
  apply hh.trans
  apply Real.exp_le_exp.mpr
  linarith

end SemAC02.Supplement.P2MRandomGraphFixedBoundary
end

section
-- Inlined Solutions.P2MGraphSparsificationProbability

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MGraphSparsificationProbability

open ACirc P2MGraphSparsificationProjection P2MBottomMonomialSupport
open P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds

attribute [local instance] Classical.propDecidable

noncomputable def monomialPool {m n : ℕ} (π : List (ACirc (ZMod 2) (CompleteEdge m n))) :
    Finset (CompleteEdge m n →₀ ℕ) :=
  open Classical in (π.flatMap bottomPolys).toFinset.biUnion (fun b => (mlz b.toPoly).support)

def Good {m n : ℕ} (π : List (ACirc (ZMod 2) (CompleteEdge m n)))
    (G : PCNonBool.BipGraph (Fin m) (Fin n)) (w : ℕ) : Prop :=
  ∀ c∈π, ∀ b∈bottomPolys c, ∀ s∈(mlz b.toPoly).support, w < s.support.card → ¬ Alive G s

 theorem pool_card {m n : ℕ} (π : List (ACirc (ZMod 2) (CompleteEdge m n)))
    (hπ : ∀ c∈π, IsSPSP ⊤ c) : (monomialPool π).card ≤ csize π := by
  classical
  let U := π.toFinset.biUnion subterms
  have hsub : monomialPool π⊆U.image (fun c => AC02Frege.sqfree (exponent c)) := by
    intro s hs
    obtain ⟨b,hb,hs⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨c,hc,hbc⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hb)
    have hparent := P2MBottomMonomialSize.bottom_parent c (hπ c hc) b hbc
    obtain ⟨g,hg,hsg⟩ := bottom_support b hparent.1 s hs
    exact Finset.mem_image.mpr ⟨g,Finset.mem_biUnion.mpr
      ⟨c,List.mem_toFinset.mpr hc,hparent.2 g hg⟩,hsg.symm⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

 theorem alive_probability (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (s : CompleteEdge (2*n) n →₀ ℕ) :
    prob p (fun x : Fin n×Fin (2*n) → Bool => decide (Alive (P2MRandomGraphFixedBoundary.graph n x) s)) ≤ p^s.support.card := by
  classical
  let f : CompleteEdge (2*n) n → Fin n×Fin (2*n) := fun e => (e.1.2,e.1.1)
  have hf : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  let S := s.support.image f
  have hc : S.card=s.support.card := Finset.card_image_of_injective _ hf
  have hb := mono p hp hp1
    (fun x : Fin n×Fin (2*n) → Bool => decide (Alive (P2MRandomGraphFixedBoundary.graph n x) s))
    (fun x => decide (∀ i∈S, x i=true)) (by
      intro x hx
      have hAlive := of_decide_eq_true hx
      apply decide_eq_true
      intro i hi
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
      exact hAlive.1 e he)
  simpa only [all_on_subset,hc] using hb

 theorem failure_probability (n w : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (π : List (ACirc (ZMod 2) (CompleteEdge (2*n) n))) (hπ : ∀ c∈π, IsSPSP ⊤ c) :
    prob p (fun x : Fin n×Fin (2*n) → Bool => decide (¬ Good π (P2MRandomGraphFixedBoundary.graph n x) w)) ≤
      (csize π : ℝ)*p^(w+1) := by
  classical
  let A := (monomialPool π).filter (fun s => w < s.support.card)
  have hcover : ∀ x : Fin n×Fin (2*n) → Bool,
      decide (¬ Good π (P2MRandomGraphFixedBoundary.graph n x) w)=true →
      ∃ s∈A, decide (Alive (P2MRandomGraphFixedBoundary.graph n x) s)=true := by
    intro x hx
    have hbad := of_decide_eq_true hx
    unfold Good at hbad
    push_neg at hbad
    obtain ⟨c,hc,b,hb,s,hs,hbig,hAlive⟩ := hbad
    refine ⟨s,Finset.mem_filter.mpr ⟨?_,hbig⟩,decide_eq_true hAlive⟩
    exact Finset.mem_biUnion.mpr ⟨b,List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨c,hc,hb⟩),hs⟩
  have hb := union_bound p hp hp1 A _
    (fun s x => decide (Alive (P2MRandomGraphFixedBoundary.graph n x) s)) hcover
  apply hb.trans
  calc
    _ ≤ ∑ _s∈A, p^(w+1) := by
      apply Finset.sum_le_sum
      intro s hs
      apply (alive_probability n p hp hp1 s).trans
      exact pow_le_pow_of_le_one hp hp1 (by have hh := (Finset.mem_filter.mp hs).2; omega)
    _ = (A.card : ℝ)*p^(w+1) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (csize π : ℝ)*p^(w+1) := by
      have hh : A.card ≤ csize π := Finset.card_filter_le _ _ |>.trans (pool_card π hπ)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hh) (pow_nonneg hp _)

end SemAC02.Supplement.P2MGraphSparsificationProbability
end

section
-- Inlined Solutions.P2MRandomGraphBoundaryExpansion

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomGraphBoundaryExpansion

open Finset P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds P2MRandomGraphFixedBoundary

 theorem single_size (n Δ s t : ℕ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ) (hΔn : Δ ≤ n)
    (hBudget : (4 : ℝ)*Δ*s ≤ n) (ht : t ≤ s) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool => decide (∃ S : Finset (Fin (2*n)),
      S.card=t ∧ ((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(t : ℝ)*Δ/4)) ≤
      ((2*n).choose t : ℝ)*Real.exp (-((t : ℝ)*Δ)/6) := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : (0 : ℝ) ≤ (Δ : ℝ)/n := by positivity
  have hp1 : (Δ : ℝ)/n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hΔn)
  let A := (univ : Finset (Fin (2*n))).powersetCard t
  have hc : A.card=(2*n).choose t := by simp [A]
  have hb := union_bound ((Δ : ℝ)/n) hp0 hp1 A
    (fun x : Fin n×Fin (2*n) → Bool => decide (∃ S : Finset (Fin (2*n)),
      S.card=t ∧ ((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(t : ℝ)*Δ/4))
    (fun S x => decide (((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(S.card : ℝ)*Δ/4)) (by
      intro x hx
      obtain ⟨S,hSc,hbad⟩ := of_decide_eq_true hx
      exact ⟨S,by simp [A,hSc],by simpa only [hSc] using (decide_eq_true hbad)⟩)
  apply hb.trans
  calc
    _ ≤ ∑ _S∈A, Real.exp (-((t : ℝ)*Δ)/6) := by
      apply sum_le_sum
      intro S hS
      have hSc : S.card=t := (mem_powersetCard.mp hS).2
      have hSmall : (S.card : ℝ)*(Δ : ℝ)/n ≤ 1/4 := by
        rw [hSc]
        apply (div_le_iff₀ hnR).mpr
        have htR : (t : ℝ) ≤ s := by exact_mod_cast ht
        nlinarith [mul_le_mul_of_nonneg_left htR (Nat.cast_nonneg (α:=ℝ) Δ)]
      simpa only [hSc] using failure_bound n Δ hn hΔ hΔn S hSmall
    _ = _ := by rw [sum_const,nsmul_eq_mul,hc]

 theorem geometric_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (s : ℕ) :
    (∑ j∈range s, q^(j+1)) ≤ q/(1-q) := by
  have hp : (∑ j∈range s, q^j) ≤ 1/(1-q) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-q)).mpr
    have he := geom_sum_mul q s
    have hpow := pow_nonneg hq0 s
    nlinarith
  calc
    _ = q*(∑ j∈range s, q^j) := by rw [mul_sum]; simp only [pow_succ',mul_comm]
    _ ≤ q*(1/(1-q)) := mul_le_mul_of_nonneg_left hp hq0
    _ = _ := by ring

 theorem failure_probability (n Δ s : ℕ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ) (hΔn : Δ ≤ n)
    (hBudget : (4 : ℝ)*Δ*s ≤ n) (hSmall : (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6)<1) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool => decide (∃ S : Finset (Fin (2*n)),
      S.Nonempty ∧ S.card ≤ s ∧ ((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(S.card : ℝ)*Δ/4)) ≤
        ((2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))/(1-(2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6)) := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : (0 : ℝ) ≤ (Δ : ℝ)/n := by positivity
  have hp1 : (Δ : ℝ)/n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hΔn)
  have hb := union_bound ((Δ : ℝ)/n) hp0 hp1 (range s)
    (fun x : Fin n×Fin (2*n) → Bool => decide (∃ S : Finset (Fin (2*n)),
      S.Nonempty ∧ S.card ≤ s ∧ ((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(S.card : ℝ)*Δ/4))
    (fun j x => decide (∃ S : Finset (Fin (2*n)), S.card=j+1 ∧
      ((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<((j+1 : ℕ) : ℝ)*Δ/4)) (by
      intro x hx
      obtain ⟨S,hS,hSs,hbad⟩ := of_decide_eq_true hx
      have hSc := card_pos.mpr hS
      refine ⟨S.card-1,mem_range.mpr (by omega),?_⟩
      apply decide_eq_true
      refine ⟨S,by omega,?_⟩
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ S.card)] using hbad)
  apply hb.trans
  apply le_trans _ (geometric_bound ((2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6)) (by positivity) hSmall s)
  apply sum_le_sum
  intro j hj
  have hjs : j+1 ≤ s := by have hh := mem_range.mp hj; omega
  apply (single_size n Δ s (j+1) hn hΔ hΔn hBudget hjs).trans
  have hchoose : ((2*n).choose (j+1) : ℝ) ≤ (2*(n : ℝ))^(j+1) := by
    exact_mod_cast Nat.choose_le_pow (2*n) (j+1)
  calc
    _ ≤ (2*(n : ℝ))^(j+1)*Real.exp (-(((j+1 : ℕ) : ℝ)*Δ)/6) :=
      mul_le_mul_of_nonneg_right hchoose (Real.exp_pos _).le
    _ = _ := by
      conv_rhs => rw [mul_pow,←Real.exp_nat_mul]
      congr 1
      congr 1
      push_cast
      ring

end SemAC02.Supplement.P2MRandomGraphBoundaryExpansion
end

section
-- Inlined Solutions.P2MBernoulliCoordinates

set_option maxHeartbeats 1000000

namespace SemAC02.P2MBernoulliCoordinates

open P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds

 theorem bit_probability {J : Type} [Fintype J] [DecidableEq J] (p : ℝ) (j : J) :
    prob p (fun x : J → Bool => x j)=p := by
  have hh := all_on_subset p ({j} : Finset J)
  simpa using hh

 theorem marginal {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (p : ℝ) (j : J) (E : (I → Bool) → Bool) :
    prob p (fun x : I×J → Bool => E (fun i => x (i,j)))=prob p E := by
  have hh := transform_blocks p (fun z : J → Bool => z j) E
  rwa [bit_probability] at hh

 theorem other_marginal {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (p : ℝ) (i : I) (E : (J → Bool) → Bool) :
    prob p (fun x : I×J → Bool => E (fun j => x (i,j)))=prob p E := by
  have hh := marginal p i E
  have he := prob_equiv (Equiv.prodComm J I) p
    (fun x : J×I → Bool => E (fun j => x (j,i)))
  exact he.trans hh

end SemAC02.P2MBernoulliCoordinates
end

section
-- Inlined Solutions.P2MRandomGraphDegreeBounds

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomGraphDegreeBounds

open Finset P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds P2MRandomGraphFixedBoundary

 theorem pigeon_tail (n Δ : ℕ) (hn : 1 ≤ n) (hΔn : Δ ≤ n) (u : Fin (2*n)) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool =>
      decide (2*Δ<(PCNonBool.nbrOn (graph n x) univ u).card)) ≤ Real.exp (-(Δ : ℝ)/3) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  let p := (Δ : ℝ)/n
  let E := fun z : Fin n → Bool => decide (2*Δ<hammingWeight z)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hΔn)
  have hmean : (n : ℝ)*p=Δ := by dsimp [p]; field_simp
  change prob p (fun x : Fin n×Fin (2*n) → Bool => E (fun v => x (v,u))) ≤ _
  rw [P2MBernoulliCoordinates.marginal,prob_fin]
  have hb := P2MBernoulliMultiplicativeTail.upper_twice p hp0 hp1 E (by
    intro z hz
    have ht : (2 : ℝ)*Δ<(hammingWeight z : ℝ) := by exact_mod_cast of_decide_eq_true hz
    have he : 2*p*(n : ℝ)=2*Δ := by nlinarith [hmean]
    rw [he]
    exact ht.le)
  rwa [hmean] at hb

 theorem hole_tail (n Δ : ℕ) (hn : 1 ≤ n) (hΔn : Δ ≤ n) (v : Fin n) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool =>
      decide (4*Δ<(univ.filter (fun u => (graph n x).Adj u v)).card)) ≤ Real.exp (-(2*(Δ : ℝ))/3) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  let p := (Δ : ℝ)/n
  let E := fun z : Fin (2*n) → Bool => decide (4*Δ<hammingWeight z)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hΔn)
  have hmean : ((2*n : ℕ) : ℝ)*p=2*Δ := by push_cast; dsimp [p]; field_simp
  change prob p (fun x : Fin n×Fin (2*n) → Bool => E (fun u => x (v,u))) ≤ _
  rw [P2MBernoulliCoordinates.other_marginal,prob_fin]
  have hb := P2MBernoulliMultiplicativeTail.upper_twice p hp0 hp1 E (by
    intro z hz
    have ht : (4 : ℝ)*Δ<(hammingWeight z : ℝ) := by exact_mod_cast of_decide_eq_true hz
    have he : 2*p*((2*n : ℕ) : ℝ)=4*Δ := by nlinarith [hmean]
    rw [he]
    exact ht.le)
  rwa [hmean] at hb

 theorem pigeons_failure (n Δ : ℕ) (hn : 1 ≤ n) (hΔn : Δ ≤ n) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool =>
      decide (∃ u, 2*Δ<(PCNonBool.nbrOn (graph n x) univ u).card)) ≤
        (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/3) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hb := union_bound ((Δ : ℝ)/n) (by positivity) ((div_le_one hnR).mpr (by exact_mod_cast hΔn))
    (univ : Finset (Fin (2*n)))
    (fun x : Fin n×Fin (2*n) → Bool => decide (∃ u, 2*Δ<(PCNonBool.nbrOn (graph n x) univ u).card))
    (fun u x => decide (2*Δ<(PCNonBool.nbrOn (graph n x) univ u).card)) (by
      intro x hx
      obtain ⟨u,hu⟩ := of_decide_eq_true hx
      exact ⟨u,mem_univ _,decide_eq_true hu⟩)
  apply hb.trans
  calc
    _ ≤ ∑ _u : Fin (2*n), Real.exp (-(Δ : ℝ)/3) := sum_le_sum (fun u hu => pigeon_tail n Δ hn hΔn u)
    _ = _ := by simp

 theorem holes_failure (n Δ : ℕ) (hn : 1 ≤ n) (hΔn : Δ ≤ n) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool =>
      decide (∃ v, 4*Δ<(univ.filter (fun u => (graph n x).Adj u v)).card)) ≤
        (n : ℝ)*Real.exp (-(2*(Δ : ℝ))/3) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hb := union_bound ((Δ : ℝ)/n) (by positivity) ((div_le_one hnR).mpr (by exact_mod_cast hΔn))
    (univ : Finset (Fin n))
    (fun x : Fin n×Fin (2*n) → Bool => decide (∃ v, 4*Δ<(univ.filter (fun u => (graph n x).Adj u v)).card))
    (fun v x => decide (4*Δ<(univ.filter (fun u => (graph n x).Adj u v)).card)) (by
      intro x hx
      obtain ⟨v,hv⟩ := of_decide_eq_true hx
      exact ⟨v,mem_univ _,decide_eq_true hv⟩)
  apply hb.trans
  calc
    _ ≤ ∑ _v : Fin n, Real.exp (-(2*(Δ : ℝ))/3) := sum_le_sum (fun v hv => hole_tail n Δ hn hΔn v)
    _ = _ := by simp

end SemAC02.Supplement.P2MRandomGraphDegreeBounds
end

section
-- Inlined Solutions.P2MRandomGraphGoodEvent

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MRandomGraphGoodEvent

open Finset P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds P2MRandomGraphFixedBoundary

attribute [local instance] Classical.propDecidable

noncomputable def Good (n Δ : ℕ) (x : Fin n×Fin (2*n) → Bool) : Prop :=
  IsBdryExp (graph n x) (P2MGraphPHPParameters.supportSize n Δ) ((Δ : ℝ)/4) ∧
    (∀ u, (PCNonBool.nbrOn (graph n x) univ u).card ≤ 2*Δ) ∧
    (∀ v, (univ.filter (fun u => (graph n x).Adj u v)).card ≤ 4*Δ)

 theorem probability_lower (n Δ : ℕ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ) (hΔn : Δ ≤ n)
    (hSmall : (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6)<1) :
    1-(((2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))/(1-(2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))+
      (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/3)+(n : ℝ)*Real.exp (-(2*(Δ : ℝ))/3)) ≤
      prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool => decide (Good n Δ x)) := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hΔR : (0 : ℝ)<Δ := by exact_mod_cast (show 0 < Δ by omega)
  let s := P2MGraphPHPParameters.supportSize n Δ
  let F : Fin 3 → (Fin n×Fin (2*n) → Bool) → Bool := fun i x =>
    if i=0 then decide (∃ S : Finset (Fin (2*n)), S.Nonempty ∧ S.card ≤ s ∧
      ((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(S.card : ℝ)*Δ/4)
    else if i=1 then decide (∃ u, 2*Δ<(PCNonBool.nbrOn (graph n x) univ u).card)
    else decide (∃ v, 4*Δ<(univ.filter (fun u => (graph n x).Adj u v)).card)
  have hcover : ∀ x : Fin n×Fin (2*n) → Bool, decide (¬ Good n Δ x)=true →
      ∃ i∈(univ : Finset (Fin 3)), F i x=true := by
    intro x hx
    have hbad := of_decide_eq_true hx
    by_cases hExp : IsBdryExp (graph n x) s ((Δ : ℝ)/4)
    · by_cases hL : ∀ u, (PCNonBool.nbrOn (graph n x) univ u).card ≤ 2*Δ
      · have hR : ¬ ∀ v, (univ.filter (fun u => (graph n x).Adj u v)).card ≤ 4*Δ :=
          fun hR => hbad ⟨hExp,hL,hR⟩
        push_neg at hR
        exact ⟨2,mem_univ _,by simpa [F] using hR⟩
      · push_neg at hL
        exact ⟨1,mem_univ _,by simpa [F] using hL⟩
    · unfold IsBdryExp at hExp
      push_neg at hExp
      obtain ⟨S,hSs,hSbad⟩ := hExp
      have hS : S.Nonempty := by
        by_contra hh
        have he : S=∅ := not_nonempty_iff_eq_empty.mp hh
        subst S
        simp [PCNonBool.boundaryOn] at hSbad
      refine ⟨0,mem_univ _,?_⟩
      simp only [F,ite_true]
      apply decide_eq_true
      exact ⟨S,hS,by exact_mod_cast hSs,by nlinarith⟩
  have hb := union_bound ((Δ : ℝ)/n) (by positivity) ((div_le_one hnR).mpr (by exact_mod_cast hΔn))
    (univ : Finset (Fin 3)) (fun x : Fin n×Fin (2*n) → Bool => decide (¬ Good n Δ x)) F hcover
  have hBudget : (4 : ℝ)*Δ*s ≤ n := by
    have hs : (s : ℝ) ≤ (n : ℝ)/(4*Δ) := Nat.floor_le (by positivity)
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ)<4*Δ)).mp hs
    nlinarith
  have hB := P2MRandomGraphBoundaryExpansion.failure_probability n Δ s hn hΔ hΔn hBudget hSmall
  have hL := P2MRandomGraphDegreeBounds.pigeons_failure n Δ hn hΔn
  have hR := P2MRandomGraphDegreeBounds.holes_failure n Δ hn hΔn
  have hSum : (∑ i : Fin 3, prob ((Δ : ℝ)/n) (F i)) ≤
      ((2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))/(1-(2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))+
      (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/3)+(n : ℝ)*Real.exp (-(2*(Δ : ℝ))/3) := by
    simpa [Fin.sum_univ_succ,F,add_assoc] using add_le_add (add_le_add hB hL) hR
  have hComp : prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool => decide (¬ Good n Δ x))=
      1-prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool => decide (Good n Δ x)) := by
    convert prob_complement ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool => decide (Good n Δ x)) using 1
    congr 1
    funext x
    simp
  linarith [hb.trans hSum]

end SemAC02.Supplement.P2MRandomGraphGoodEvent
end

section
-- Inlined Solutions.P2MRandomGraphErrorBounds

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomGraphErrorBounds

open P2MBernoulliProduct P2MRandomGraphGoodEvent

attribute [local instance] Classical.propDecidable

 theorem exp_neg_nat_log (n k : ℕ) (hn : 1 ≤ n) :
    Real.exp (-((k : ℝ)*Real.log (n : ℝ)))=1/(n : ℝ)^k := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log hnR,one_div]

 theorem tail_base (n Δ : ℕ) (hn : 1 ≤ n) (hΔ : 24*Real.log n ≤ (Δ : ℝ)) :
    (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6) ≤ 2/(n : ℝ)^3 := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have he : Real.exp (-(Δ : ℝ)/6) ≤ 1/(n : ℝ)^4 := by
    rw [←exp_neg_nat_log n 4 hn]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    linarith
  calc
    _ ≤ (2*(n : ℝ))*(1/(n : ℝ)^4) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by field_simp <;> ring

 theorem total_error (n Δ : ℕ) (hn : 2 ≤ n) (hΔ : 24*Real.log n ≤ (Δ : ℝ)) :
    (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6)<1 ∧
      ((2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))/(1-(2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))+
        (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/3)+(n : ℝ)*Real.exp (-(2*(Δ : ℝ))/3) ≤ 7/(n : ℝ)^3 := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  let q := (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq := tail_base n Δ (by omega) hΔ
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn3 : (8 : ℝ) ≤ (n : ℝ)^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn2 3
    norm_num at hh
    exact hh
  have hqhalf : q ≤ 1/2 := by
    apply hq.trans
    exact (div_le_iff₀ (by positivity : (0 : ℝ)<(n : ℝ)^3)).mpr (by linarith)
  have hq1 : q < 1 := by linarith
  have hgeom : q/(1-q) ≤ 2*q := (div_le_iff₀ (by linarith : 0 < 1-q)).mpr (by nlinarith)
  have hD0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
  have hL : (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/3) ≤ q :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
  have hR : (n : ℝ)*Real.exp (-(2*(Δ : ℝ))/3) ≤ q/2 := by
    have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (show -(2*(Δ : ℝ))/3 ≤ -(Δ : ℝ)/6 by nlinarith)) hnR.le
    dsimp [q]
    nlinarith
  refine ⟨hq1,?_⟩
  change q/(1-q)+(2*(n : ℝ))*Real.exp (-(Δ : ℝ)/3)+(n : ℝ)*Real.exp (-(2*(Δ : ℝ))/3) ≤ _
  have hqr : q ≤ 2/(n : ℝ)^3 := hq
  simp only [div_eq_mul_inv] at hqr hgeom hL hR ⊢
  nlinarith

 theorem probability_lower (n Δ : ℕ) (hn : 2 ≤ n) (hΔ : 1 ≤ Δ) (hΔn : Δ ≤ n)
    (hΔlog : 24*Real.log n ≤ (Δ : ℝ)) :
    1-7/(n : ℝ)^3 ≤ prob ((Δ : ℝ)/n)
      (fun x : Fin n×Fin (2*n) → Bool => decide (P2MRandomGraphGoodEvent.Good n Δ x)) := by
  classical
  obtain ⟨hSmall,hErr⟩ := total_error n Δ hn hΔlog
  have hh := P2MRandomGraphGoodEvent.probability_lower n Δ (by omega) hΔ hΔn hSmall
  linarith

end SemAC02.Supplement.P2MRandomGraphErrorBounds
end

section
-- Inlined Solutions.P2MBernoulliIntersection

namespace SemAC02.P2MBernoulliIntersection

open Finset P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds

 theorem lower {I : Type} [Fintype I] [DecidableEq I] (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (E F : (I → Bool) → Bool) : prob p E+prob p F-1 ≤ prob p (fun x => E x && F x) := by
  classical
  have hb := union_bound p hp hp1 (univ : Finset Bool) (fun x => !(E x && F x))
    (fun b x => if b then !E x else !F x) (by
      intro x hx
      by_cases he : E x=true
      · exact ⟨false,mem_univ _,by simpa [he] using hx⟩
      · exact ⟨true,mem_univ _,by simp [he]⟩)
  have hh : prob p (fun x => !(E x && F x)) ≤ prob p (fun x => !E x)+prob p (fun x => !F x) := by
    simpa [Fintype.sum_bool,add_comm] using hb
  rw [prob_complement,prob_complement,prob_complement] at hh
  linarith

end SemAC02.P2MBernoulliIntersection
end

section
-- Inlined Solutions.P2MGraphSparsificationExistence

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MGraphSparsificationExistence

open ACirc P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds
open P2MGraphSparsificationProjection

 theorem good_graph (n w : ℕ) (hn : 2 ≤ n) (hΔ : 1 ≤ php74Delta n) (hΔn : php74Delta n ≤ n)
    (hΔlog : 24*Real.log n ≤ (php74Delta n : ℝ))
    (π : List (ACirc (ZMod 2) (CompleteEdge (2*n) n))) (hπ : ∀ c∈π, IsSPSP ⊤ c)
    (hSmall : (csize π : ℝ)*((php74Delta n : ℝ)/n)^(w+1)+7/(n : ℝ)^3<1) :
    ∃ G : PCNonBool.BipGraph (Fin (2*n)) (Fin n), Lemma74Concl G ∧
      P2MGraphSparsificationProbability.Good π G w := by
  classical
  let p := (php74Delta n : ℝ)/n
  let E := fun x : Fin n×Fin (2*n) → Bool => decide (Lemma74Concl (P2MRandomGraphFixedBoundary.graph n x))
  let F := fun x : Fin n×Fin (2*n) → Bool =>
    decide (P2MGraphSparsificationProbability.Good π (P2MRandomGraphFixedBoundary.graph n x) w)
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hΔn)
  have hGoodGraph : 1-7/(n : ℝ)^3 ≤ prob p E :=
    P2MRandomGraphErrorBounds.probability_lower n (php74Delta n) hn hΔ hΔn hΔlog
  have hSparse := P2MGraphSparsificationProbability.failure_probability n w p hp0 hp1 π hπ
  have hComp : prob p (fun x : Fin n×Fin (2*n) → Bool =>
      decide (¬ P2MGraphSparsificationProbability.Good π (P2MRandomGraphFixedBoundary.graph n x) w))=1-prob p F := by
    convert prob_complement p F using 1
    congr 1
    funext x
    simp [F]
  rw [hComp] at hSparse
  have hIntersect := P2MBernoulliIntersection.lower p hp0 hp1 E F
  have hPos : 0 < prob p (fun x => E x && F x) := by
    change (csize π : ℝ)*p^(w+1)+7/(n : ℝ)^3<1 at hSmall
    linarith
  obtain ⟨x,hx⟩ := positive_exists p _ hPos
  refine ⟨P2MRandomGraphFixedBoundary.graph n x,?_⟩
  simpa only [Bool.and_eq_true,decide_eq_true_eq,E,F] using hx

end SemAC02.Supplement.P2MGraphSparsificationExistence
end

section
-- Inlined Solutions.P2MGraphSparsificationCircuits

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphSparsificationCircuits

open MvPolynomial ACirc P2MArithmeticCircuitBasics P2MPolynomialArithmeticCircuits P2MGraphSparsificationProjection

variable {m n D : ℕ}

noncomputable def bottom (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (d : ℕ) (c : ACirc (ZMod 2) (CompleteEdge m n)) : ACirc (ZMod 2) (Fin n×Fin D) :=
  polynomialCircuit (project G ι d c.toPoly)

noncomputable def term (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (d : ℕ) : ACirc (ZMod 2) (CompleteEdge m n) → ACirc (ZMod 2) (Fin n×Fin D)
  | .prod cs => .prod (cs.map (bottom G ι d))
  | _ => .prod []

noncomputable def line (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (d : ℕ) : ACirc (ZMod 2) (CompleteEdge m n) → ACirc (ZMod 2) (Fin n×Fin D)
  | .sum ps => .sum (ps.map (fun p => (p.1,term G ι d p.2)))
  | _ => .sum []

theorem term_layer (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (d : ℕ) (t : ACirc (ZMod 2) (CompleteEdge m n)) :
    IsProdOf (IsSumOf (IsMonGate (d : ℕ∞))) (term G ι d t) := by
  cases t <;> try exact fun c hc => (List.not_mem_nil hc).elim
  case prod cs =>
    intro c hc
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
    exact polynomial_layer _ d (project_degree G ι d b.toPoly)

theorem line_layer (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (d : ℕ) (c : ACirc (ZMod 2) (CompleteEdge m n)) :
    IsSPSP (d : ℕ∞) (line G ι d c) := by
  cases c <;> try exact fun p hp => (List.not_mem_nil hp).elim
  case sum ps =>
    intro p hp
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
    exact term_layer G ι d z.2

theorem prod_value (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (d : ℕ) (cs : List (ACirc (ZMod 2) (CompleteEdge m n)))
    (hgood : ∀ b∈cs, ∀ s∈(mlz b.toPoly).support, d < s.support.card → ¬ Alive G s) (x : Fin n×Fin D → Bool) (hx : nDivOmega n D x) :
    cval (term G ι d (.prod cs)) x=cval (.prod cs) (liftPoint G ι x) := by
  simp only [term,cval_prod,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro b hb
  change polyFn (polynomialCircuit (project G ι d b.toPoly)).toPoly x=cval b (liftPoint G ι x)
  rw [polynomial_poly]
  exact project_value G ι d b.toPoly (hgood b hb) x hx

theorem line_value (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (d : ℕ) (c : ACirc (ZMod 2) (CompleteEdge m n))
    (hc : IsSPSP ⊤ c)
    (hgood : ∀ b∈bottomPolys c, ∀ s∈(mlz b.toPoly).support, d < s.support.card → ¬ Alive G s)
    (x : Fin n×Fin D → Bool) (hx : nDivOmega n D x) : cval (line G ι d c) x=cval c (liftPoint G ι x) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    simp only [line,cval_sum,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro p hp
    congr 1
    have hterm := hc p hp
    cases ht : p.2 with
    | var i => simp only [ht,IsProdOf] at hterm
    | const a => simp only [ht,IsProdOf] at hterm
    | sum qs => simp only [ht,IsProdOf] at hterm
    | prod cs =>
      refine prod_value G ι d cs ?_ x hx
      intro b hb s hs hbig
      apply hgood b _ s hs hbig
      exact List.mem_flatMap.mpr ⟨p,hp,by simp only [ht]; exact hb⟩

theorem top_terms (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (d : ℕ) (c : ACirc (ZMod 2) (CompleteEdge m n)) :
    topTerms (line G ι d c)=(topTerms c).map (term G ι d) := by
  cases c <;> simp [line,topTerms,List.map_map,Function.comp_def]

theorem term_value (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (d : ℕ) (c t : ACirc (ZMod 2) (CompleteEdge m n))
    (hc : IsSPSP ⊤ c) (ht : t∈topTerms c)
    (hgood : ∀ b∈bottomPolys c, ∀ s∈(mlz b.toPoly).support, d < s.support.card → ¬ Alive G s)
    (x : Fin n×Fin D → Bool) (hx : nDivOmega n D x) : cval (term G ι d t) x=cval t (liftPoint G ι x) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ht
    have hterm := hc p hp
    cases ht : p.2 with
    | var i => simp only [ht,IsProdOf] at hterm
    | const a => simp only [ht,IsProdOf] at hterm
    | sum qs => simp only [ht,IsProdOf] at hterm
    | prod cs =>
      refine prod_value G ι d cs ?_ x hx
      intro b hb s hs hbig
      apply hgood b _ s hs hbig
      exact List.mem_flatMap.mpr ⟨p,hp,by simp only [ht]; exact hb⟩

end SemAC02.Supplement.P2MGraphSparsificationCircuits
end

section
-- Inlined Solutions.P2MGraphSparsificationInputs

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MGraphSparsificationInputs

open MvPolynomial P2MGraphSparsificationProjection

variable {m n D : ℕ}

 theorem pigeon_value (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (u : Fin m)
    (y : Fin n×Fin D → Bool) :
    polyFn (∏ v∈(PCNonBool.nbrOn (completeBip m n) Finset.univ u).attach,
      (1-xE (completeBip m n) u v.1 (by simpa [PCNonBool.nbrOn] using v.2))) (liftPoint G ι y)=
    polyFn (∏ v∈(PCNonBool.nbrOn G Finset.univ u).attach,
      (1-X (v.1,ι v.1 ⟨u,by simpa [PCNonBool.nbrOn] using v.2⟩))) y := by
  classical
  let f : Fin n → ZMod 2 := fun v => 1-boolPt (liftPoint G ι y) (⟨(u,v),trivial⟩ : CompleteEdge m n)
  have hSource : polyFn (∏ v∈(PCNonBool.nbrOn (completeBip m n) Finset.univ u).attach,
      (1-xE (completeBip m n) u v.1 (by simpa [PCNonBool.nbrOn] using v.2))) (liftPoint G ι y)=
      ∏ v : Fin n, f v := by
    simp only [polyFn,map_prod,map_sub,map_one,xE,eval_X]
    change (∏ v∈(PCNonBool.nbrOn (completeBip m n) Finset.univ u).attach, f v.1)=_
    rw [Finset.prod_attach]
    have hN : PCNonBool.nbrOn (completeBip m n) Finset.univ u=Finset.univ := by
      ext v
      constructor
      · intro hv
        exact Finset.mem_univ _
      · intro hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,trivial⟩
    rw [hN]
  have hTarget : polyFn (∏ v∈(PCNonBool.nbrOn G Finset.univ u).attach,
      (1-X (v.1,ι v.1 ⟨u,by simpa [PCNonBool.nbrOn] using v.2⟩))) y=
      ∏ v∈PCNonBool.nbrOn G Finset.univ u, f v := by
    simp only [polyFn,map_prod,map_sub,map_one,eval_X]
    have he : (∏ v∈(PCNonBool.nbrOn G Finset.univ u).attach,
        (1-(boolPt y (v.1,ι v.1 ⟨u,by simpa [PCNonBool.nbrOn] using v.2⟩) : ZMod 2)))=
        ∏ v∈(PCNonBool.nbrOn G Finset.univ u).attach, f v.1 := by
      apply Finset.prod_congr rfl
      intro v hv
      have huv : G.Adj u v.1 := by simpa [PCNonBool.nbrOn] using v.2
      simp [f,boolPt,liftPoint,huv]
    rw [he,Finset.prod_attach]
  rw [hSource,hTarget]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro v hv hn
  have hnG : ¬ G.Adj u v := by simpa [PCNonBool.nbrOn] using hn
  simp [f,liftPoint,hnG,boolPt]

 theorem input_projection (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D)
    (p : MvPolynomial (CompleteEdge m n) (ZMod 2)) (hp : p∈phpG (completeBip m n)) :
    (∃ p'∈phpPadded G ι, ∀ y : Fin n×Fin D → Bool, nDivOmega n D y →
      polyFn p (liftPoint G ι y)=polyFn p' y) ∨
    (∀ y : Fin n×Fin D → Bool, nDivOmega n D y → polyFn p (liftPoint G ι y)=0) := by
  classical
  rcases hp with ⟨u,rfl⟩ | ⟨u,u',v,h,h',hne,rfl⟩
  · left
    refine ⟨∏ v∈(PCNonBool.nbrOn G Finset.univ u).attach,
      (1-X (v.1,ι v.1 ⟨u,by simpa [PCNonBool.nbrOn] using v.2⟩)),Or.inr ⟨u,rfl⟩,?_⟩
    intro y hy
    exact pigeon_value G ι u y
  · right
    intro y hy
    have hneE : (⟨(u,v),h⟩ : CompleteEdge m n)≠⟨(u',v),h'⟩ := by
      intro he
      exact hne (congrArg (fun e : CompleteEdge m n => e.1.1) he)
    have hz := pair_zero G ι y hy (⟨(u,v),h⟩ : CompleteEdge m n) ⟨(u',v),h'⟩ rfl hneE
    simp only [polyFn,map_mul,xE,eval_X]
    rcases hz with hz | hz
    · rw [hz,zero_mul]
    · rw [hz,mul_zero]

end SemAC02.Supplement.P2MGraphSparsificationInputs
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
-- Inlined Solutions.P2MProjectedTopSize

namespace SemAC02.Supplement.P2MProjectedTopSize

open ACirc

 theorem bound {F V U : Type} [CommRing F]
    (Ω : Set (U → Bool)) (M τ : ACirc F V → ACirc F U)
    (π : List (ACirc F V)) (hterms : ∀ c, topTerms (M c)=(topTerms c).map τ) :
    topS Ω (π.map M) ≤ csize π := by
  classical
  let S := π.toFinset.biUnion subterms
  have hsub : P2MProofTopFunctions.pool Ω (π.map M)⊆S.image (fun t => fun x : Ω => cval (τ t) x.1) := by
    intro g hg
    obtain ⟨hn,c',hc',t',ht',he⟩ := (P2MProofTopFunctions.mem_pool Ω (π.map M) g).mp hg
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hc'
    rw [hterms c] at ht'
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp ht'
    exact Finset.mem_image.mpr ⟨t,Finset.mem_biUnion.mpr
      ⟨c,List.mem_toFinset.mpr hc,P2MArithmeticTopSize.top_term_subterm c t ht⟩,he⟩
  rw [←P2MProofTopFunctions.card_eq_topS]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end SemAC02.Supplement.P2MProjectedTopSize
end

section
-- Inlined Solutions.P2MGraphSparsificationProof

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MGraphSparsificationProof

open MvPolynomial ACirc P2MGraphSparsificationProjection P2MGraphSparsificationCircuits

 theorem refutation {m n D : ℕ} (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (w : ℕ)
    (π : List (ACirc (ZMod 2) (CompleteEdge m n)))
    (hπ : IsSemPCRef (IsSPSP ⊤) Set.univ (polyAx (phpG (completeBip m n))) π)
    (hgood : P2MGraphSparsificationProbability.Good π G w) :
    IsSemPCRef (IsSPSP (w : ℕ∞)) (nDivOmega n D) (polyAx (phpPadded G ι)) (π.map (line G ι w)) := by
  have hvalue : ∀ c∈π, ∀ y, nDivOmega n D y → cval (line G ι w c) y=cval c (liftPoint G ι y) :=
    fun c hc y hy => line_value G ι w c (hπ.1 c hc) (hgood c hc) y hy
  refine ⟨?_,?_,?_⟩
  · intro c hc
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    exact line_layer G ι w a
  · intro i hi
    have hi' : i < π.length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map]
    rcases hπ.2.1 i hi' with ⟨a,ha,he⟩ | he | ⟨j,l,hj,hl,he⟩
    · obtain ⟨p,hp,rfl⟩ := ha
      rcases P2MGraphSparsificationInputs.input_projection G ι p hp with ⟨p',hp',hinput⟩ | hzero
      · left
        refine ⟨polyFn p',⟨p',hp',rfl⟩,?_⟩
        intro y hy
        rw [hvalue _ (List.getElem_mem hi') y hy,he (liftPoint G ι y) (Set.mem_univ _),hinput y hy]
      · right; left
        intro y hy
        rw [hvalue _ (List.getElem_mem hi') y hy,he (liftPoint G ι y) (Set.mem_univ _),hzero y hy]
    · right; left
      intro y hy
      rw [hvalue _ (List.getElem_mem hi') y hy,he (liftPoint G ι y) (Set.mem_univ _)]
    · right; right
      refine ⟨j,l,hj,hl,?_⟩
      intro y hy hp hq
      rw [hvalue _ (List.getElem_mem hi') y hy]
      apply he (liftPoint G ι y) (Set.mem_univ _)
      · rwa [hvalue _ (List.getElem_mem (hj.trans hi')) y hy] at hp
      · rwa [hvalue _ (List.getElem_mem (hl.trans hi')) y hy] at hq
  · obtain ⟨c,hc,hval⟩ := hπ.2.2
    refine ⟨line G ι w c,?_,?_⟩
    · rw [List.getLast?_map,hc]
      rfl
    · intro y hy
      rw [hvalue c (List.mem_of_getLast? hc) y hy]
      exact hval (liftPoint G ι y) (Set.mem_univ _)

 theorem top_bound {m n D : ℕ} (G : PCNonBool.BipGraph (Fin m) (Fin n))
    (ι : ∀ v : Fin n, {u : Fin m // G.Adj u v} ↪ Fin D) (w : ℕ)
    (π : List (ACirc (ZMod 2) (CompleteEdge m n))) :
    topS (nDivOmega n D) (π.map (line G ι w)) ≤ csize π :=
  P2MProjectedTopSize.bound (nDivOmega n D) (line G ι w) (term G ι w) π (top_terms G ι w)

end SemAC02.Supplement.P2MGraphSparsificationProof
end

section
-- Inlined Solutions.P2MGraphHoleEmbeddings

namespace SemAC02.Supplement.P2MGraphHoleEmbeddings

 theorem exists_injections {L : Type} [Fintype L] {n D : ℕ}
    (G : PCNonBool.BipGraph L (Fin n))
    (hR : ∀ v, (Finset.univ.filter (fun u => G.Adj u v)).card ≤ D) :
    Nonempty (∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) := by
  classical
  have he : ∀ v : Fin n, Nonempty ({u : L // G.Adj u v} ↪ Fin D) := by
    intro v
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_fin,Fintype.card_subtype] using hR v
  exact ⟨fun v => Classical.choice (he v)⟩

end SemAC02.Supplement.P2MGraphHoleEmbeddings
end

section
-- Inlined Solutions.P2MCompleteUnaryPHPLowerBound

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MCompleteUnaryPHPLowerBound

open ACirc Filter P2MGraphSparsificationProjection

theorem full (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ π : List (ACirc (ZMod 2) (Edge (completeBip (2 * n) n))),
        IsSemPCRef (IsSPSP ⊤) Set.univ (polyAx (phpG (completeBip (2 * n) n))) π →
        Real.exp (γ * Real.log n ^ 2 / Real.log (Real.log n)) ≤ csize π  := by
  obtain ⟨a,C,ha,hC,n₀,hBase⟩ := theorem_7_5_graph_php_bounded_bottom
  obtain ⟨w,hParameters⟩ := P2MGraphSparsificationAsymptoticParameters.eventually_valid a C γ ha hC hγ0 hγ1
  obtain ⟨n₁,hn₁⟩ := eventually_atTop.mp hParameters
  refine ⟨max n₀ n₁,?_⟩
  intro n hn π hπ
  rcases hn₁ n ((le_max_right n₀ n₁).trans hn) with ⟨hn2,hΔ,hΔn,hΔlog,hw,hwRange,hSuccess,hDominates⟩
  by_contra hh
  have hM : (csize π : ℝ)<Real.exp (γ*Real.log n^2/Real.log (Real.log n)) := lt_of_not_ge hh
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : (0 : ℝ) ≤ (php74Delta n : ℝ)/n := by positivity
  have hSmall : (csize π : ℝ)*((php74Delta n : ℝ)/n)^(w n+1)+7/(n : ℝ)^3<1 := by
    have hm := mul_le_mul_of_nonneg_right hM.le (pow_nonneg hp0 (w n+1))
    linarith
  obtain ⟨G,hG,hGood⟩ := P2MGraphSparsificationExistence.good_graph n (w n) hn2 hΔ hΔn hΔlog π hπ.1 hSmall
  obtain ⟨ι⟩ := P2MGraphHoleEmbeddings.exists_injections G hG.2.2
  let π' := π.map (P2MGraphSparsificationCircuits.line G ι (w n))
  have hπ' : IsSemPCRef (IsSPSP (w n : ℕ∞)) (nDivOmega n (4*php74Delta n)) (polyAx (phpPadded G ι)) π' :=
    P2MGraphSparsificationProof.refutation G ι (w n) π hπ hGood
  have hLower := (hBase n ((le_max_left n₀ n₁).trans hn) G hG (w n) hw hwRange).2 ι π' hπ'
  have hSize : (topS (nDivOmega n (4*php74Delta n)) π' : ℝ) ≤ csize π := by
    exact_mod_cast P2MGraphSparsificationProof.top_bound G ι (w n) π
  exact (not_lt_of_ge (hDominates.trans (hLower.trans hSize))) hM

end SemAC02.Supplement.P2MCompleteUnaryPHPLowerBound
end

end P2MCompleteUnaryPHPProof
open SemAC02.Supplement MvPolynomial ACirc Filter Topology

theorem solution (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ π : List (ACirc (ZMod 2) (Edge (completeBip (2 * n) n))),
        IsSemPCRef (IsSPSP ⊤) Set.univ (polyAx (phpG (completeBip (2 * n) n))) π →
        Real.exp (γ * Real.log n ^ 2 / Real.log (Real.log n)) ≤ csize π  := by
  exact P2MCompleteUnaryPHPProof.SemAC02.Supplement.P2MCompleteUnaryPHPLowerBound.full γ hγ0 hγ1
