-- Prove2me | solution 1 for SemAC02.theorem_8_1_lifted_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T03:09:12.524196+00:00
-- url     : https://prove2.me/submissions/659a90f4-8877-4375-85ac-41561035b888

import Mathlib
import Definitions.Def_SemAC02_Circ
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Theorems.Thm_SemAC02_lemma_8_7_gadget_dimension
import Definitions.Def_SemAC02_IsSemRefutation
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_IsRelPseudoRed
import Theorems.Thm_SemAC02_corollary_4_18_frege_size_bound
import Definitions.Def_SemAC02_arith
import Definitions.Def_SemAC02_lift
import Definitions.Def_AC02Frege_PC
import Definitions.Def_SemAC02_naiveRelPR
import Theorems.Thm_SemAC02_lemma_8_4_degree_transfer
import Definitions.Def_SemAC02_IsGadget
import Theorems.Thm_SemAC02_proposition_8_3_lift_unsat
import Definitions.Def_SemAC02_PCDegreeAtLeast
import Definitions.Def_PCNonBool_IsRefutation

open _root_.SemAC02 hiding pcAxioms
open _root_.AC02Frege _root_.LiftSAParity
namespace P2MRootProof
section
-- Inlined Solutions.P2MCoinShiftParameters

set_option maxHeartbeats 1000000

namespace SemAC02.P2MCoinShiftParameters

theorem shift_pos {ε : ℝ} (hε : 0 < ε) : 0 < ε/(1+ε) := div_pos hε (by linarith)

theorem shift_lt {ε : ℝ} (hε : 0 < ε) : ε/(1+ε) < ε := by
  apply (div_lt_iff₀ (by linarith : (0 : ℝ) < 1+ε)).mpr
  nlinarith [sq_pos_of_pos hε]

theorem shifted_scale_bound {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1) {d : ℕ} (hd : 2 ≤ d) :
    (ε/(1+ε))^(-1/((d : ℝ)-1)) ≤ 2*ε^(-1/((d : ℝ)-1)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  let e := 1/((d : ℝ)-1)
  have he : e ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < (d : ℝ)-1)).mpr (by linarith)
  have hexp : -1/((d : ℝ)-1) = -e := by dsimp only [e]; ring
  rw [hexp]
  have hden : 0 < 1+ε := by linarith
  have hident : (ε/(1+ε))^(-e) = ε^(-e)*(1+ε)^e := by
    rw [Real.div_rpow hε₀.le hden.le,Real.rpow_neg hden.le,div_inv_eq_mul]
  have hpow : (1+ε)^e ≤ 2 :=
    (Real.rpow_le_self_of_one_le (by linarith) he).trans (by linarith)
  rw [hident]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hε₀.le (-e))

theorem scale_ge_one {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1) {d : ℕ} (hd : 2 ≤ d) :
    1 ≤ ε^(-1/((d : ℝ)-1)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε₀ hε
  exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)

/-- Absorb the root-normalisation overhead into the source's uniform exponential constant. -/
theorem size_absorption {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1) {d : ℕ} (hd : 2 ≤ d)
    (A : ℝ) (s : ℕ) (hs : (s : ℝ) ≤ Real.exp (A*(ε/(1+ε))^(-1/((d : ℝ)-1)))) :
    ((s+1 : ℕ) : ℝ) ≤ Real.exp ((2*(abs A)+1)*ε^(-1/((d : ℝ)-1))) := by
  let L := ε^(-1/((d : ℝ)-1))
  let L' := (ε/(1+ε))^(-1/((d : ℝ)-1))
  have hL : 1 ≤ L := scale_ge_one hε₀ hε hd
  have hL' : 0 ≤ L' := Real.rpow_nonneg (shift_pos hε₀).le _
  have hbound : L' ≤ 2*L := shifted_scale_bound hε₀ hε hd
  have hcoeff : A*L' ≤ (2*(abs A))*L := by
    calc
      _ ≤ (abs A)*L' := mul_le_mul_of_nonneg_right (le_abs_self A) hL'
      _ ≤ (abs A)*(2*L) := mul_le_mul_of_nonneg_left hbound (abs_nonneg A)
      _ = _ := by ring
  have hs' : (s : ℝ) ≤ Real.exp ((2*(abs A))*L) := hs.trans (Real.exp_le_exp.mpr hcoeff)
  have hP : 1 ≤ Real.exp ((2*(abs A))*L) := Real.one_le_exp_iff.mpr (by positivity)
  have hE : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  calc
    _ = (s : ℝ)+1 := by simp
    _ ≤ Real.exp ((2*(abs A))*L)+1 := by linarith
    _ ≤ 2*Real.exp ((2*(abs A))*L) := by linarith
    _ ≤ Real.exp ((2*(abs A))*L)*Real.exp L := by
      nlinarith [mul_le_mul_of_nonneg_left hE (Real.exp_nonneg ((2*(abs A))*L))]
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [L]; ring

end SemAC02.P2MCoinShiftParameters
end

section
-- Inlined Solutions.P2MCoveringDimension

set_option maxHeartbeats 1000000

namespace SemAC02.P2MCoveringDimension

theorem scale_power {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 2 ≤ d) :
    (ε^(-1/((d : ℝ)-1)))^(d-1) = ε⁻¹ := by
  have hr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdn : (d : ℝ)-1 ≠ 0 := by linarith
  rw [← Real.rpow_mul_natCast hε.le,Nat.cast_sub (by omega : 1 ≤ d),Nat.cast_one]
  rw [show (-1/((d : ℝ)-1))*((d : ℝ)-1) = -1 by field_simp]
  exact Real.rpow_neg_one ε

theorem scale_dimension_identity {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 2 ≤ d) :
    (ε^(-1/((d : ℝ)-1)))^(2*d-1)*ε^2 = ε^(-1/((d : ℝ)-1)) := by
  rw [show 2*d-1 = (d-1)*2+1 by omega,pow_succ,pow_mul,scale_power hε hd]
  field_simp

theorem small_parameter_scale {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) {d : ℕ} (hd : 2 ≤ d)
    (hsmall : ε < 1/C^(d-1)) : C ≤ ε^(-1/((d : ℝ)-1)) := by
  have hcpos : 0 < C^(d-1) := pow_pos hC _
  have hprod : ε*C^(d-1) < 1 := (lt_div_iff₀ hcpos).mp hsmall
  have hp : C^(d-1) < (ε^(-1/((d : ℝ)-1)))^(d-1) := by
    rw [scale_power hε hd]
    have h := (lt_div_iff₀ hε).mpr (show C^(d-1)*ε < (1 : ℝ) from by nlinarith)
    simpa only [one_div] using h
  by_contra! hn
  have hle := pow_le_pow_left₀ (Real.rpow_nonneg hε.le _) hn.le (d-1)
  linarith

theorem smallest_odd_upper {x : ℝ} (hx : 3 ≤ x) {m : ℕ} (hm : Odd m) (hxm : x ≤ (m : ℝ))
    (hmin : ∀ m' : ℕ, Odd m' → x ≤ (m' : ℝ) → m ≤ m') : (m : ℝ) < x+2 := by
  have hm3 : 3 ≤ m := by exact_mod_cast (show (3 : ℝ) ≤ (m : ℝ) from hx.trans hxm)
  by_contra! hn
  have hodd : Odd (m-2) := Nat.Odd.sub_even (by omega) hm (by decide : Even 2)
  have hdown : x ≤ ((m-2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ m),Nat.cast_ofNat]
    linarith
  have h := hmin (m-2) hodd hdown
  omega

theorem dimension_bounds {L : ℝ} (hL : 1 ≤ L) (n : ℕ) {m : ℕ} (hm : Odd m)
    (hml : 128*L^n ≤ (m : ℝ))
    (hmin : ∀ m' : ℕ, Odd m' → 128*L^n ≤ (m' : ℝ) → m ≤ m') :
    1 ≤ m ∧ (m : ℝ) ≤ 130*L^n := by
  have hp : 1 ≤ L^n := one_le_pow₀ hL
  have hx : (3 : ℝ) ≤ 128*L^n := by nlinarith
  have hu := smallest_odd_upper hx hm hml hmin
  constructor
  · have h : (1 : ℝ) ≤ (m : ℝ) := by nlinarith
    exact_mod_cast h
  · nlinarith

theorem dimension_tail_exponent {ε : ℝ} (hε : 0 < ε) {d m : ℕ} (hd : 2 ≤ d)
    (hm : 128*(ε^(-1/((d : ℝ)-1)))^(2*d-1) ≤ (m : ℝ)) :
    2*ε^(-1/((d : ℝ)-1)) ≤ (m : ℝ)*ε^2/64 := by
  have h := mul_le_mul_of_nonneg_right hm (sq_nonneg ε)
  rw [mul_assoc,scale_dimension_identity hε hd] at h
  nlinarith

end SemAC02.P2MCoveringDimension
end

section
-- Inlined Solutions.P2MLiftedParameterFoundations

set_option maxHeartbeats 1000000

open Filter Topology

namespace SemAC02.P2MLiftedParameterFoundations

theorem exists_smallest_odd (x : ℝ) :
    ∃ m : ℕ, Odd m ∧ x ≤ (m : ℝ) ∧ ∀ m' : ℕ, Odd m' → x ≤ (m' : ℝ) → m ≤ m' := by
  classical
  have hex : ∃ m : ℕ, Odd m ∧ x ≤ (m : ℝ) := by
    refine ⟨2*⌈x⌉₊+1,⟨⌈x⌉₊,by omega⟩,?_⟩
    have h := Nat.le_ceil x
    norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith [show (0 : ℝ) ≤ ⌈x⌉₊ from Nat.cast_nonneg _]
  exact ⟨Nat.find hex,(Nat.find_spec hex).1,(Nat.find_spec hex).2,
    fun m' hm' hx => Nat.find_min' hex ⟨hm',hx⟩⟩

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

theorem scale_inverse_power {d : ℕ} (hd : 2 ≤ d) {L : ℝ} (hL : 0 < L) :
    ((L^(d-1))⁻¹)^(-1/((d : ℝ)-1)) = L := by
  have hε : 0 < (L^(d-1))⁻¹ := inv_pos.mpr (pow_pos hL _)
  apply (pow_left_inj₀ (Real.rpow_nonneg hε.le _) hL.le (by omega : d-1 ≠ 0)).mp
  simpa only [inv_inv] using P2MCoveringDimension.scale_power hε hd

theorem epsilon_small {d : ℕ} (hd : 2 ≤ d) {L ε₀ : ℝ}
    (hL : 1 ≤ L) (hε₀ : 0 < ε₀) (hlarge : 1/ε₀ < L) : (L^(d-1))⁻¹ < ε₀ := by
  have hLpos : 0 < L := by linarith
  have hp : L ≤ L^(d-1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (by omega : 1 ≤ d-1)
  calc
    _ ≤ L⁻¹ := (inv_le_inv₀ (pow_pos hLpos _) hLpos).mpr hp
    _ < ε₀ := by
      rw [← one_div]
      exact (div_lt_iff₀ hLpos).mpr (by have h := (div_lt_iff₀ hε₀).mp hlarge; nlinarith)

theorem gadget_polynomial_size {n m a : ℕ} (hn : 1 ≤ n) (g : Circ (Fin m)) (A : ℝ)
    (ha : 32*A ≤ (a : ℝ)) (hsize : (g.treeSize : ℝ) ≤ Real.exp (A*(32*Real.log n))) :
    g.treeSize ≤ n^a := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hs : (g.treeSize : ℝ) ≤ (n : ℝ)^a := by
    calc
      _ ≤ Real.exp (A*(32*Real.log n)) := hsize
      _ ≤ Real.exp (Real.log n*(a : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = (n : ℝ)^a := by rw [← Real.rpow_natCast,Real.rpow_def_of_pos hnpos]
  exact_mod_cast hs

end SemAC02.P2MLiftedParameterFoundations
end

section
-- Inlined Solutions.P2MLiftedGadgetSelection

set_option maxHeartbeats 2000000

open Filter

namespace SemAC02.P2MLiftedGadgetSelection

open P2MLiftedParameterFoundations

/-- The Section 8 gadget, with a polynomial tree-size bound and explicit polylogarithmic
dimension. The exponent is chosen using only d, before all CNF parameters. -/
theorem polynomial_gadgets (d : ℕ) (hd : 2 ≤ d) :
    ∃ a : ℕ, ∀ᶠ n : ℕ in atTop,
      let L := 32*Real.log (n : ℝ)
      let ε := (L^(d-1))⁻¹
      ∃ (m : ℕ) (g : Circ (Fin m)), 0 < ε ∧ ε ≤ 1/256 ∧ IsGadget d g ∧
        g.treeSize ≤ n^a ∧ 128*L^(2*d-1) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 130*L^(2*d-1) ∧
        ∀ k : ℕ, (k : ℝ) ≤ (1/2-ε)*((n*m : ℕ) : ℝ) →
          1-(((n*m : ℕ) : ℝ)+1)*n*Real.exp (-L) ≤
            (Module.finrank (ZMod 2) (multiplierSpace (fun X => g.eval X) n k) : ℝ)/
              (Hn (n*m) k : ℝ) := by
  obtain ⟨A,ε₀,hε₀,hgadget⟩ := lemma_8_7_gadget_dimension d hd
  let e := min ε₀ (1/256 : ℝ)
  have he : 0 < e := lt_min hε₀ (by norm_num)
  refine ⟨⌈32*A⌉₊,?_⟩
  filter_upwards [eventually_ge_atTop 2,eventually_log_large (2+1/e)] with n hn hlog
  let L := 32*Real.log (n : ℝ)
  let ε := (L^(d-1))⁻¹
  have hL : 1 ≤ L := by dsimp [L]; have heinv := one_div_pos.mpr he; nlinarith
  have hLpos : 0 < L := by linarith
  have hlarge : 1/e < L := by dsimp [L]; have heinv := one_div_pos.mpr he; nlinarith
  have hεpos : 0 < ε := inv_pos.mpr (pow_pos hLpos _)
  have hεsmall : ε < e := epsilon_small hd hL he hlarge
  have hεsmall₀ : ε < ε₀ := hεsmall.trans_le (min_le_left _ _)
  have hεmax : ε ≤ 1/256 := hεsmall.le.trans (min_le_right _ _)
  have hscale : ε^(-1/((d : ℝ)-1)) = L := scale_inverse_power hd hLpos
  obtain ⟨m,hm,hml,hmin⟩ := exists_smallest_odd (128*L^(2*d-1))
  have hml' : 128*(ε^(-1/((d : ℝ)-1)))^(2*d-1) ≤ (m : ℝ) := by rw [hscale]; exact hml
  have hmin' : ∀ m' : ℕ, Odd m' → 128*(ε^(-1/((d : ℝ)-1)))^(2*d-1) ≤ (m' : ℝ) → m ≤ m' := by
    simpa only [hscale] using hmin
  obtain ⟨g,hg,hsize,hdim⟩ := hgadget ε hεpos hεsmall₀ hεmax m hm hml' hmin'
  rw [hscale] at hsize hdim
  have hpoly : g.treeSize ≤ n^⌈32*A⌉₊ :=
    gadget_polynomial_size (by omega) g A (Nat.le_ceil (32*A)) hsize
  have hmhi := (P2MCoveringDimension.dimension_bounds hL (2*d-1) hm hml hmin).2
  exact ⟨m,g,hεpos,hεmax,hg,hpoly,hml,hmhi,hdim n (by omega)⟩

end SemAC02.P2MLiftedGadgetSelection
end

section
-- Inlined Solutions.P2MLiftedApproximationParameters

set_option maxHeartbeats 2000000

namespace SemAC02.P2MLiftedApproximationParameters

/-- A uniform rounded lower-level approximation parameter. All depth dependence is isolated
in the natural exponent p; the constant 1/16 is independent of every input parameter. -/
theorem lower_parameter (p : ℕ) (hp : 1 ≤ p) (z y : ℝ)
    (hy : (8 : ℝ)^p ≤ y) (hyz : y ≤ z) :
    let u := y^((1 : ℝ)/(p : ℝ))
    let ε := ((32*z)^p)⁻¹
    ∃ r : ℕ, 1 ≤ r ∧ z*u/32 ≤ (r : ℝ) ∧ (r : ℝ) ≤ z^2 ∧
      128*ε*(r : ℝ)^p ≤ y/4 ∧ 128*ε*(r : ℝ)^(p-1) ≤ 1 := by
  let u := y^((1 : ℝ)/(p : ℝ))
  let ε := ((32*z)^p)⁻¹
  have hpne : p ≠ 0 := by omega
  have h8 : (8 : ℝ) ≤ (8 : ℝ)^p := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) hp
  have hypos : 0 < y := by linarith
  have hzpos : 0 < z := by linarith
  have hup : u^p = y := by
    dsimp [u]
    rw [← Real.rpow_mul_natCast hypos.le]
    have hpcast : (p : ℝ) ≠ 0 := by exact_mod_cast hpne
    rw [div_mul_cancel₀ _ hpcast,Real.rpow_one]
  have hu0 : 0 ≤ u := Real.rpow_nonneg hypos.le _
  have hu8 : 8 ≤ u := (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 8) hu0 hpne).mp (by rw [hup]; exact hy)
  have huy : u ≤ y := by
    rw [← hup]
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ u) hp
  have huz : u ≤ z := huy.trans hyz
  let t := z*u/16
  let r := ⌊t⌋₊
  have ht : 2 ≤ t := by dsimp [t]; nlinarith
  have hr : 1 ≤ r := by apply Nat.le_floor; norm_num only [Nat.cast_one]; linarith
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hrupper : (r : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hrlower : t/2 ≤ (r : ℝ) := by have h := Nat.lt_floor_add_one t; change t < (r : ℝ)+1 at h; linarith
  have hrz : (r : ℝ) ≤ z^2 := by dsimp [t] at hrupper; nlinarith
  have hry : y/4 ≤ (r : ℝ) := by dsimp [t] at hrlower; nlinarith
  have h512 : (512 : ℝ) ≤ (512 : ℝ)^p := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 512) hp
  have hpow : (r : ℝ)^p*(512 : ℝ)^p ≤ (32*z)^p*y := by
    calc
      _ ≤ t^p*(512 : ℝ)^p := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0 hrupper p) (by positivity)
      _ = (t*512)^p := (mul_pow _ _ _).symm
      _ = ((32*z)*u)^p := congrArg (fun a : ℝ => a^p) (by dsimp [t]; ring)
      _ = _ := by rw [mul_pow,hup]
  have hpow' : 512*(r : ℝ)^p ≤ (32*z)^p*y := by
    calc
      _ = (r : ℝ)^p*512 := by ring
      _ ≤ (r : ℝ)^p*(512 : ℝ)^p := mul_le_mul_of_nonneg_left h512 (pow_nonneg hr0 p)
      _ ≤ _ := hpow
  have hLp : 0 < (32*z)^p := pow_pos (by positivity) _
  have hdiv : (512*(r : ℝ)^p)/(32*z)^p ≤ y := (div_le_iff₀ hLp).mpr (by nlinarith [hpow'])
  have htop : 128*ε*(r : ℝ)^p ≤ y/4 := by
    have he : 128*ε*(r : ℝ)^p = ((512*(r : ℝ)^p)/(32*z)^p)/4 := by dsimp [ε]; ring
    rw [he]
    linarith
  have hstep : 128*ε*(r : ℝ)^(p-1)*(r : ℝ) = 128*ε*(r : ℝ)^p := by
    rw [mul_assoc,← pow_succ,show p-1+1 = p by omega]
  have hbottom : 128*ε*(r : ℝ)^(p-1) ≤ 1 := by
    have hh : (128*ε*(r : ℝ)^(p-1))*(r : ℝ) ≤ (r : ℝ) := by rw [hstep]; exact htop.trans hry
    nlinarith
  refine ⟨r,hr,?_,hrz,htop,hbottom⟩
  simpa only [t,u,div_div,show (16 : ℝ)*2 = 32 from by norm_num] using hrlower

end SemAC02.P2MLiftedApproximationParameters
end

section
-- Inlined Solutions.P2MLiftedTopParameter

set_option maxHeartbeats 2000000

namespace SemAC02.P2MLiftedTopParameter

/-- Choose the top approximation parameter by integer division. The resulting PC-degree
gap is exact; a square-exponential budget controls the top-layer error. -/
theorem top_parameter (p r Δ : ℕ) (hr : 1 ≤ r) (E : ℝ)
    (hE : 12*(r : ℝ)^(p+1) ≤ E) (hEeq : E^2 = (Δ : ℝ)) :
    ∃ R : ℕ, 1 ≤ R ∧ 3*(R*r^p)+1 < Δ ∧ (r : ℝ)*E ≤ (R : ℝ) := by
  have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrp : (1 : ℝ) ≤ (r : ℝ)^p := one_le_pow₀ hrr
  have hrp' : (1 : ℝ) ≤ (r : ℝ)^(p+1) := one_le_pow₀ hrr
  have hE12 : 12 ≤ E := by linarith
  have hEpos : 0 < E := by linarith
  have hErp : 12*(r : ℝ)^p ≤ E :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hrr (Nat.le_succ p)) (by norm_num)).trans hE
  let Q := 6*r^p
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hQΔ : Q ≤ Δ := by
    have hh : (Q : ℝ) ≤ (Δ : ℝ) := by
      dsimp [Q]
      push_cast
      nlinarith
    exact_mod_cast hh
  let R := Δ/Q
  have hR : 1 ≤ R := Nat.div_pos hQΔ hQpos
  have hdiv := Nat.lt_mul_div_succ Δ hQpos
  have hmul := Nat.mul_div_le Δ Q
  change Δ < Q*(R+1) at hdiv
  change Q*R ≤ Δ at hmul
  have hq1 : 1 ≤ R*r^p := by
    have hp1 : 1 ≤ r^p := one_le_pow₀ hr
    nlinarith
  have hgap : 3*(R*r^p)+1 < Δ := by dsimp [Q] at hmul; nlinarith
  have hDupper : (Δ : ℝ) ≤ (R : ℝ)*(12*(r : ℝ)^p) := by
    have hh : Δ ≤ 12*(R*r^p) := by dsimp [Q] at hdiv; nlinarith
    exact_mod_cast (by nlinarith [hh] : Δ ≤ R*(12*r^p))
  have hDlower : (r : ℝ)*E*(12*(r : ℝ)^p) ≤ (Δ : ℝ) := by
    calc
      _ = E*(12*(r : ℝ)^(p+1)) := by rw [pow_succ]; ring
      _ ≤ E*E := mul_le_mul_of_nonneg_left hE hEpos.le
      _ = _ := by nlinarith [hEeq]
  have hfac : 0 < 12*(r : ℝ)^p := by positivity
  exact ⟨R,hR,hgap,(mul_le_mul_iff_left₀ hfac).mp (hDlower.trans hDupper)⟩

theorem top_error_bound {p r R : ℕ} {ε y : ℝ}
    (hR : (r : ℝ)*Real.exp (y/2) ≤ (R : ℝ))
    (htop : 128*ε*(r : ℝ)^p ≤ y/2) :
    (r : ℝ) ≤ (R : ℝ)*Real.exp (-(128*ε*(r : ℝ)^p)) := by
  have he : 1 ≤ Real.exp (y/2-(128*ε*(r : ℝ)^p)) := Real.one_le_exp_iff.mpr (by linarith)
  calc
    _ ≤ (r : ℝ)*Real.exp (y/2-(128*ε*(r : ℝ)^p)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he (Nat.cast_nonneg r)
    _ = ((r : ℝ)*Real.exp (y/2))*Real.exp (-(128*ε*(r : ℝ)^p)) := by rw [Real.exp_sub,Real.exp_neg]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hR (Real.exp_pos _).le

end SemAC02.P2MLiftedTopParameter
end

section
-- Inlined Solutions.P2MLiftedAsymptoticParameters

set_option maxHeartbeats 2000000

open Filter

namespace SemAC02.P2MLiftedAsymptoticParameters

theorem eventual_parameters (d : ℕ) (hd : 2 ≤ d) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ Δ : ℕ, (n : ℝ)^C ≤ (Δ : ℝ) → Δ ≤ n →
      let z := Real.log (n : ℝ)
      let y := Real.log (Δ : ℝ)
      let u := y^((1 : ℝ)/((d-1 : ℕ) : ℝ))
      let ε := ((32*z)^(d-1))⁻¹
      ∃ r R : ℕ, 1 ≤ r ∧ 1 ≤ R ∧ 3*(R*r^(d-1))+1 < Δ ∧
        z*u/32 ≤ (r : ℝ) ∧ 128*ε*(r : ℝ)^(d-2) ≤ 1 ∧
        (r : ℝ) ≤ (R : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-1))) ∧
        ε*(r : ℝ)^(d-1) ≤ 32*z ∧ 1 ≤ (Real.exp (-1)/128)*(z*u) := by
  let p := d-1
  let c := Real.exp (-1)/128
  have hp : 1 ≤ p := by dsimp [p]; omega
  have hc : 0 < c := by dsimp [c]; positivity
  filter_upwards [eventually_ge_atTop 2,
    P2MLiftedParameterFoundations.eventually_log_large (max ((8 : ℝ)^p/C) (1/c)),
    P2MLiftedParameterFoundations.eventually_log_power_le 12 (2*d) (by linarith : 0 < C/2)]
    with n hn hlog hdom
  intro Δ hlow hupp
  let z := Real.log (n : ℝ)
  let y := Real.log (Δ : ℝ)
  let u := y^((1 : ℝ)/(p : ℝ))
  let ε := ((32*z)^p)⁻¹
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hΔp : 0 < (Δ : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hnp C) hlow
  have hCy : C*z ≤ y := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hnp C) hlow
    rw [Real.log_rpow hnp] at h
    exact h
  have hyz : y ≤ z := Real.log_le_log hΔp (by exact_mod_cast hupp)
  have hzlarge : max ((8 : ℝ)^p/C) (1/c) ≤ z := hlog
  have hy : (8 : ℝ)^p ≤ y :=
    ((div_le_iff₀ hC).mp ((le_max_left _ _).trans hzlarge)).trans (by nlinarith)
  have h8 : (8 : ℝ) ≤ (8 : ℝ)^p := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) hp
  have hypos : 0 < y := by linarith
  have hzpos : 0 < z := by linarith
  obtain ⟨r,hr,hrT,hrz,htop,hbottom⟩ := P2MLiftedApproximationParameters.lower_parameter p hp z y hy hyz
  have hEr : 12*(r : ℝ)^(p+1) ≤ Real.exp (y/2) := by
    calc
      _ ≤ 12*(z^2)^(p+1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg r) hrz _) (by norm_num)
      _ = 12*z^(2*d) := by rw [← pow_mul]; congr 2; dsimp [p]; omega
      _ ≤ (n : ℝ)^(C/2) := hdom
      _ = Real.exp (z*C/2) := by rw [Real.rpow_def_of_pos hnp]; congr 1; dsimp [z]; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hEeq : (Real.exp (y/2))^2 = (Δ : ℝ) := by
    calc
      _ = Real.exp (y/2)*Real.exp (y/2) := by ring
      _ = Real.exp (y/2+y/2) := (Real.exp_add _ _).symm
      _ = Real.exp y := congrArg Real.exp (by ring)
      _ = _ := Real.exp_log hΔp
  obtain ⟨R,hR,hgap,hRE⟩ := P2MLiftedTopParameter.top_parameter p r Δ hr _ hEr hEeq
  have htop' : (r : ℝ) ≤ (R : ℝ)*Real.exp (-(128*ε*(r : ℝ)^p)) :=
    P2MLiftedTopParameter.top_error_bound hRE (htop.trans (by linarith))
  have hbudget : ε*(r : ℝ)^p ≤ 32*z := by nlinarith [htop]
  have hu1 : 1 ≤ u := Real.one_le_rpow (by linarith : 1 ≤ y) (by positivity)
  have hcz : 1 ≤ c*z := by
    have h := (div_le_iff₀ hc).mp ((le_max_right _ _).trans hzlarge)
    nlinarith
  have hlarge : 1 ≤ c*(z*u) := by nlinarith
  have hbottom' : 128*ε*(r : ℝ)^(d-2) ≤ 1 := by
    simpa only [p,show d-1-1 = d-2 by omega] using hbottom
  exact ⟨r,R,hr,hR,hgap,hrT,hbottom',htop',hbudget,hlarge⟩

end SemAC02.P2MLiftedAsymptoticParameters
end

section
-- Inlined Solutions.P2MLiftedDimensionBudgets

set_option maxHeartbeats 2000000

namespace SemAC02.P2MLiftedDimensionBudgets

theorem dimension_budgets {d n m r : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n)
    {ε L : ℝ} (hε : 0 < ε) (hL : 1 ≤ L)
    (hscale : ε^(-1/((d : ℝ)-1)) = L)
    (hm : 128*L^(2*d-1) ≤ (m : ℝ)) (hr : ε*(r : ℝ)^(d-1) ≤ L) :
    16/ε^2 ≤ ((n*m : ℕ) : ℝ) ∧ (r : ℝ)^(d-1) ≤ ε*((n*m : ℕ) : ℝ)/2 := by
  have hm' : 128*(ε^(-1/((d : ℝ)-1)))^(2*d-1) ≤ (m : ℝ) := by rw [hscale]; exact hm
  have ht := P2MCoveringDimension.dimension_tail_exponent hε hd hm'
  rw [hscale] at ht
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hvm : (m : ℝ) ≤ ((n*m : ℕ) : ℝ) := by
    push_cast
    nlinarith [Nat.cast_nonneg m (α:=ℝ)]
  have hprod := mul_le_mul_of_nonneg_right hvm (sq_nonneg ε)
  have hv : 128*L ≤ ((n*m : ℕ) : ℝ)*ε^2 := by linarith
  constructor
  · exact (div_le_iff₀ (sq_pos_of_pos hε)).mpr (by nlinarith)
  · apply (mul_le_mul_iff_left₀ hε).mp
    nlinarith

theorem density_error {n m : ℕ} (hn : 2 ≤ n) (hm : m ≤ n) :
    (((n*m : ℕ) : ℝ)+1)*n*Real.exp (-(32*Real.log (n : ℝ))) ≤ 1/2 := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmr : (m : ℝ) ≤ n := by exact_mod_cast hm
  have he : Real.exp (32*Real.log (n : ℝ)) = (n : ℝ)^32 := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos hnp]
    congr 1
    norm_num
    ring
  rw [Real.exp_neg,he]
  have h29 : (4 : ℝ) ≤ (n : ℝ)^29 := by
    have hpow := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ n) (by decide : 2 ≤ 29)
    nlinarith
  have h32 : 4*(n : ℝ)^3 ≤ (n : ℝ)^32 := by
    calc
      _ ≤ (n : ℝ)^29*(n : ℝ)^3 := mul_le_mul_of_nonneg_right h29 (by positivity)
      _ = _ := by rw [← pow_add]
  have hnum : (((n*m : ℕ) : ℝ)+1)*(n : ℝ) ≤ 2*(n : ℝ)^3 := by
    push_cast
    have hmn : (n : ℝ)*m ≤ (n : ℝ)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hmn hnp.le]
  rw [← div_eq_mul_inv]
  exact (div_le_iff₀ (pow_pos hnp 32)).mpr (by nlinarith)

end SemAC02.P2MLiftedDimensionBudgets
end

section
-- Inlined Solutions.P2MLiftedFinalExponent

set_option maxHeartbeats 1000000

namespace SemAC02.P2MLiftedFinalExponent

theorem final_exponent {r R p : ℕ} {ε T : ℝ}
    (hr : T/32 ≤ (r : ℝ)) (hbottom : 128*ε*(r : ℝ)^(p-1) ≤ 1)
    (htop : (r : ℝ) ≤ (R : ℝ)*Real.exp (-(128*ε*(r : ℝ)^p)))
    (hlarge : 1 ≤ (Real.exp (-1)/128)*T) :
    Real.exp ((Real.exp (-1)/128)*T) ≤
      (1/2)*Real.exp ((1/2)*min
        ((r : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(p-1))))
        ((R : ℝ)*Real.exp (-(128*ε*(r : ℝ)^p)))) := by
  have hepos : 0 < Real.exp (-1) := Real.exp_pos _
  have hele : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hb : (r : ℝ)*Real.exp (-1) ≤ (r : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(p-1))) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg r)
  have htr : (r : ℝ)*Real.exp (-1) ≤ (r : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hele (Nat.cast_nonneg r)
  have ht : (r : ℝ)*Real.exp (-1) ≤ (R : ℝ)*Real.exp (-(128*ε*(r : ℝ)^p)) := htr.trans htop
  have hmin := le_min hb ht
  let b := (Real.exp (-1)/128)*T
  let θ := (1/2)*min ((r : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(p-1))))
    ((R : ℝ)*Real.exp (-(128*ε*(r : ℝ)^p)))
  have hθ : 2*b ≤ θ := by
    have hh := mul_le_mul_of_nonneg_left hr (hepos.le)
    dsimp [b,θ]
    linarith
  have h2 : (2 : ℝ) ≤ Real.exp b := by
    have hone : (2 : ℝ) ≤ Real.exp 1 := by have h := Real.add_one_le_exp (1 : ℝ); linarith
    exact hone.trans (Real.exp_le_exp.mpr hlarge)
  change Real.exp b ≤ (1/2)*Real.exp θ
  calc
    _ ≤ (1/2)*(Real.exp b*Real.exp b) := by nlinarith
    _ = (1/2)*Real.exp (2*b) := by rw [two_mul,Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ) (by norm_num)

end SemAC02.P2MLiftedFinalExponent
end

section
-- Inlined Solutions.P2MCircuitRenaming

set_option maxHeartbeats 1000000

namespace SemAC02.P2MCircuitRenaming

theorem eval_rename {V W : Type} (f : V → W) (C : Circ V) (x : W → Bool) :
    (C.rename f).eval x = C.eval (x ∘ f) := by
  cases C with
  | const b => simp [Circ.rename,Circ.eval]
  | lit v b => simp [Circ.rename,Circ.eval,Function.comp_def]
  | and cs =>
    simp only [Circ.rename,Circ.eval,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename f c x
  | or cs =>
    simp only [Circ.rename,Circ.eval,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename f c x
  | xor cs =>
    simp only [Circ.rename,Circ.eval,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename f c x
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem rename_comp {U V W : Type} (f : U → V) (g : V → W) (C : Circ U) :
    (C.rename f).rename g = C.rename (g ∘ f) := by
  cases C with
  | const b => simp [Circ.rename]
  | lit v b => simp [Circ.rename,Function.comp_def]
  | and cs =>
    simp only [Circ.rename,List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact rename_comp f g c
  | or cs =>
    simp only [Circ.rename,List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact rename_comp f g c
  | xor cs =>
    simp only [Circ.rename,List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact rename_comp f g c
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem rename_id {V : Type} (C : Circ V) : C.rename id = C := by
  cases C with
  | const b => simp [Circ.rename]
  | lit v b => simp [Circ.rename]
  | and cs =>
    rw [Circ.rename]
    congr 1
    calc
      cs.map (Circ.rename id) = cs.map id := List.map_congr_left (fun c hc => rename_id c)
      _ = cs := List.map_id _
  | or cs =>
    rw [Circ.rename]
    congr 1
    calc
      cs.map (Circ.rename id) = cs.map id := List.map_congr_left (fun c hc => rename_id c)
      _ = cs := List.map_id _
  | xor cs =>
    rw [Circ.rename]
    congr 1
    calc
      cs.map (Circ.rename id) = cs.map id := List.map_congr_left (fun c hc => rename_id c)
      _ = cs := List.map_id _
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem rename_leftInverse {V W : Type} (f : V → W) (g : W → V)
    (hg : Function.LeftInverse g f) : Function.LeftInverse (Circ.rename g) (Circ.rename f) := by
  intro C
  rw [rename_comp,show g ∘ f = id from funext hg,rename_id]

theorem rename_injective {V W : Type} [Nonempty V] (f : V → W) (hf : Function.Injective f) :
    Function.Injective (Circ.rename f) :=
  (rename_leftInverse f (Function.invFun f) (Function.leftInverse_invFun hf)).injective

@[simp] theorem isAnd_rename {V W : Type} (f : V → W) (C : Circ V) :
    (C.rename f).isAnd = C.isAnd := by cases C <;> simp [Circ.rename,Circ.isAnd]
@[simp] theorem isOr_rename {V W : Type} (f : V → W) (C : Circ V) :
    (C.rename f).isOr = C.isOr := by cases C <;> simp [Circ.rename,Circ.isOr]
@[simp] theorem isXor_rename {V W : Type} (f : V → W) (C : Circ V) :
    (C.rename f).isXor = C.isXor := by cases C <;> simp [Circ.rename,Circ.isXor]

theorem monotone_rename {V W : Type} (f : V → W) {C : Circ V} (hC : IsMonotoneCirc C) :
    IsMonotoneCirc (C.rename f) := by
  induction hC with
  | const b => rw [Circ.rename]; constructor
  | lit v => rw [Circ.rename]; constructor
  | and cs hcs ih =>
    rw [Circ.rename]
    apply IsMonotoneCirc.and
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
    exact ih c' hc'
  | or cs hcs ih =>
    rw [Circ.rename]
    apply IsMonotoneCirc.or
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
    exact ih c' hc'

theorem reduced_rename {V W : Type} [Nonempty V] (f : V → W) (hf : Function.Injective f)
    {C : Circ V} (hC : IsReduced C) : IsReduced (C.rename f) := by
  induction hC with
  | const b => rw [Circ.rename]; constructor
  | lit v b => rw [Circ.rename]; constructor
  | and cs hn ht hr ih =>
    rw [Circ.rename]
    apply IsReduced.and _ (hn.map (rename_injective f hf))
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isAnd_rename] using ht c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
  | or cs hn ht hr ih =>
    rw [Circ.rename]
    apply IsReduced.or _ (hn.map (rename_injective f hf))
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isOr_rename] using ht c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
  | xor cs hn ht hr ih =>
    rw [Circ.rename]
    apply IsReduced.xor _ (hn.map (rename_injective f hf))
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isXor_rename] using ht c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'

theorem depth_rename {V W : Type} (f : V → W) (C : Circ V) :
    (C.rename f).depth = C.depth := by
  cases C with
  | const b => simp [Circ.rename,Circ.depth]
  | lit v b => simp [Circ.rename,Circ.depth]
  | and cs =>
    simp only [Circ.rename,Circ.depth,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => depth_rename f c)
  | or cs =>
    simp only [Circ.rename,Circ.depth,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => depth_rename f c)
  | xor cs =>
    simp only [Circ.rename,Circ.depth,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => depth_rename f c)
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem size_rename {V W : Type} (f : V → W) (C : Circ V) :
    (C.rename f).treeSize = C.treeSize := by
  cases C with
  | const b => simp [Circ.rename,Circ.treeSize]
  | lit v b => simp [Circ.rename,Circ.treeSize]
  | and cs =>
    simp only [Circ.rename,Circ.treeSize,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => size_rename f c)
  | or cs =>
    simp only [Circ.rename,Circ.treeSize,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => size_rename f c)
  | xor cs =>
    simp only [Circ.rename,Circ.treeSize,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => size_rename f c)
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

end SemAC02.P2MCircuitRenaming
end

section
-- Inlined Solutions.P2MCircuitVariableEquivalence

set_option maxHeartbeats 2000000

namespace SemAC02.P2MCircuitVariableEquivalence

open Classical P2MCircuitRenaming

theorem children_subcircuits {V W : Type} (f : V → W) (cs : List (Circ V))
    (h : ∀ c ∈ cs, (c.rename f).subcircuits = c.subcircuits.image (Circ.rename f)) :
    (((cs.map (Circ.rename f)).map (fun c => c.subcircuits)).foldr (· ∪ ·) ∅) =
    (((cs.map (fun c : Circ V => c.subcircuits)).foldr (· ∪ ·) ∅).image (Circ.rename f)) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons,List.foldr_cons,Finset.image_union]
    rw [h c (by simp),ih (fun a ha => h a (by simp [ha]))]

theorem subcircuits_rename {V W : Type} (f : V → W) (A : Circ V) :
    (A.rename f).subcircuits = A.subcircuits.image (Circ.rename f) := by
  cases A with
  | const b => simp [Circ.rename,Circ.subcircuits]
  | lit v b => simp [Circ.rename,Circ.subcircuits]
  | and cs =>
    rw [Circ.rename,Circ.subcircuits,Circ.subcircuits,Finset.image_insert]
    rw [Circ.rename]
    congr 1
    exact children_subcircuits f cs (fun c hc => subcircuits_rename f c)
  | or cs =>
    rw [Circ.rename,Circ.subcircuits,Circ.subcircuits,Finset.image_insert]
    rw [Circ.rename]
    congr 1
    exact children_subcircuits f cs (fun c hc => subcircuits_rename f c)
  | xor cs =>
    rw [Circ.rename,Circ.subcircuits,Circ.subcircuits,Finset.image_insert]
    rw [Circ.rename]
    congr 1
    exact children_subcircuits f cs (fun c hc => subcircuits_rename f c)
termination_by A
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem famSize_rename {V W : Type} (e : V ≃ W) (F : Finset (Circ V)) :
    famSize (F.image (Circ.rename e)) = famSize F := by
  have hi : Function.Injective (Circ.rename e) :=
    (rename_leftInverse e e.symm e.left_inv).injective
  unfold famSize
  rw [Finset.image_biUnion]
  have he : (F.biUnion (fun A => (A.rename e).subcircuits)) =
      (F.biUnion Circ.subcircuits).image (Circ.rename e) := by
    rw [Finset.biUnion_image]
    exact congrArg (Finset.biUnion F) (funext (fun A => subcircuits_rename e A))
  rw [he,Finset.card_image_of_injective _ hi]

theorem proofSize_rename {V W : Type} (e : V ≃ W) (π : List (Circ V)) :
    proofSize (π.map (Circ.rename e)) = proofSize π := by
  have he : (π.map (Circ.rename e)).toFinset = π.toFinset.image (Circ.rename e) := by
    ext A
    simp
  simpa only [proofSize,he] using famSize_rename e π.toFinset

theorem refutation_rename {V W : Type} (f : V → W) {d : ℕ} {F : Set (Circ V)}
    {π : List (Circ V)} (hπ : IsSemRefutation d F π) :
    IsSemRefutation d (Circ.rename f '' F) (π.map (Circ.rename f)) := by
  rcases hπ with ⟨hdepth,hrules,hlast⟩
  refine ⟨?_,?_,?_⟩
  · intro A hA
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
    simpa only [depth_rename] using hdepth B hB
  · intro k hk
    have hk' : k < π.length := by simpa only [List.length_map] using hk
    simp only [List.getElem_map]
    rcases hrules k hk' with ha | ht | ⟨i,j,hi,hj,hij⟩
    · exact Or.inl ⟨π[k],ha,rfl⟩
    · exact Or.inr (Or.inl (by intro x; rw [eval_rename]; exact ht _))
    · refine Or.inr (Or.inr ⟨i,j,hi,hj,?_⟩)
      intro x hi' hj'
      simp only [List.getElem_map,eval_rename] at hi' hj' ⊢
      exact hij _ hi' hj'
  · rw [List.getLast?_map,hlast]
    simp only [Option.map_some,Circ.rename]

end SemAC02.P2MCircuitVariableEquivalence
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
-- Inlined Solutions.P2MMajorityFoundation

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace AC02Frege.P2MMajorityFoundation

open Classical

noncomputable def pointPoly {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) : MvPolynomial V (ZMod 2) :=
  ∏ i : V, if i ∈ S then X i else 1 + X i

theorem pointPoly_indicator {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = MvPolynomial.indicator (fun i : V => if i ∈ S then (1 : ZMod 2) else 0) := by
  classical
  unfold pointPoly MvPolynomial.indicator
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp only [hi, ↓reduceIte, ZMod.card, Nat.reduceSub, pow_one]
  · simp only [map_one, CharTwo.sub_eq_add]
    calc
      X i = X i + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
      _ = 1 + (X i + 1) := by abel
  · simp [CharTwo.sub_eq_add]

theorem pointPoly_multilinear {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    IsMultilinear (pointPoly S) := by
  rw [pointPoly_indicator]
  apply (mem_restrictDegree V _ 1).mp
  simpa only [ZMod.card, Nat.reduceSub] using indicator_mem_restrictDegree
    (fun i : V => if i ∈ S then (1 : ZMod 2) else 0)

theorem pointPoly_eval {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) (x : V → ZMod 2) :
    eval x (pointPoly S) =
      if x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) then 1 else 0 := by
  classical
  rw [pointPoly_indicator]
  split_ifs with h
  · subst x; exact eval_indicator_apply_eq_one _
  · exact eval_indicator_apply_eq_zero _ _ h

theorem multilinear_sum {V ι : Type} (S : Finset ι) (f : ι → MvPolynomial V (ZMod 2))
    (hf : ∀ i ∈ S, IsMultilinear (f i)) : IsMultilinear (∑ i ∈ S, f i) := by
  apply (mem_restrictDegree V _ 1).mp
  exact Submodule.sum_mem _ (fun i hi => (mem_restrictDegree V (f i) 1).mpr (hf i hi))

theorem majOne_multilinear (ℓ : ℕ) : IsMultilinear (majOne ℓ) := by
  unfold majOne
  apply multilinear_sum
  intro S _
  simpa only [pointPoly] using pointPoly_multilinear S

theorem eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem point_of_ones {V : Type} [Fintype V] [DecidableEq V] (x : V → ZMod 2) :
    (fun i => if i ∈ Finset.univ.filter (fun i => x i = 1) then (1 : ZMod 2) else 0) = x := by
  classical
  funext i
  rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]

theorem ones_of_point {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    Finset.univ.filter (fun i => (if i ∈ S then (1 : ZMod 2) else 0) = 1) = S := by
  classical
  ext i
  simp

theorem majOne_eval (ℓ : ℕ) (x : Fin ℓ → ZMod 2) :
    eval x (majOne ℓ) = if ℓ / 2 < (Finset.univ.filter (fun i => x i = 1)).card
      then 1 else 0 := by
  classical
  unfold majOne
  simp only [map_sum]
  have hev (S : Finset (Fin ℓ)) := pointPoly_eval S x
  simp only [pointPoly] at hev
  simp only [hev]
  have heq (S : Finset (Fin ℓ)) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro hx; rw [hx, ones_of_point]
    · intro hS; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp

theorem heavy_monomial_absorbs_majority (ℓ : ℕ) (S : Finset (Fin ℓ))
    (hS : ℓ / 2 < S.card) : ML (xMon S * majOne ℓ) = xMon S := by
  apply multilinear_ext (ml_multilinear _) (xMon_multilinear S)
  intro x
  simp only [eval_ml, map_mul]
  by_cases hx : eval x (xMon S) = 0
  · rw [hx, zero_mul]
  · have hsub : S ⊆ Finset.univ.filter (fun i => x i = 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hxi : x i ≠ 0 := by
        intro hz
        apply hx
        rw [xMon_eval]
        exact Finset.prod_eq_zero hi hz
      rcases eq_zero_or_one (x i) with hz | ho
      · exact False.elim (hxi hz)
      · exact ho
    have hcard := Finset.card_le_card hsub
    rw [majOne_eval, if_pos (by omega), mul_one]

theorem pointPoly_factor {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = xMon S * ∏ i ∈ Finset.univ.filter (fun i : V => i ∉ S),
      (1 + X i : MvPolynomial V (ZMod 2)) := by
  simp only [pointPoly, Finset.prod_ite]
  congr 1
  rw [xMon]
  apply Finset.prod_congr
  · ext i; simp
  · intro i _; rfl

theorem support_mul_xMon_degree {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (p : MvPolynomial V (ZMod 2))
    (s : V →₀ ℕ) (hs : s ∈ (xMon S * p).support) : S.card ≤ s.sum (fun _ e => e) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (support_mul (xMon S) p hs)
  have haeq : a = Finsupp.indicator S (fun _ _ => (1 : ℕ)) := by
    rw [xMon_eq_monomial] at ha
    exact Finset.mem_singleton.mp (support_monomial_subset ha)
  subst a
  have hsum : (Finsupp.indicator S (fun _ _ => (1 : ℕ))).sum (fun _ e => e) = S.card := by
    simp only [Finsupp.sum, indicator_support]
    have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finsupp.indicator_apply, hi]
    rw [heq]; simp
  rw [← hab]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hsum]
  omega

theorem majOne_support_heavy (ℓ : ℕ) (s : Fin ℓ →₀ ℕ)
    (hs : s ∈ (majOne ℓ).support) : ℓ / 2 < s.sum (fun _ e => e) := by
  classical
  unfold majOne at hs
  obtain ⟨S, hS, hsS⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have hheavy := (Finset.mem_filter.mp hS).2
  change s ∈ (pointPoly S).support at hsS
  rw [pointPoly_factor] at hsS
  exact lt_of_lt_of_le hheavy (support_mul_xMon_degree S _ s hsS)

end AC02Frege.P2MMajorityFoundation
end

section
-- Inlined Solutions.P2MBooleanBasis

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation

namespace AC02Frege.P2MBooleanBasis

theorem squarefree_eq_indicator {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s = Finsupp.indicator s.support (fun _ _ => 1) := by
  classical
  ext i
  by_cases hi : i ∈ s.support
  · simp only [Finsupp.indicator_apply, dif_pos hi]
    have hpos := Finsupp.mem_support_iff.mp hi
    exact Nat.le_antisymm (hs i) (by omega)
  · simpa only [Finsupp.indicator_apply, dif_neg hi] using (by simpa only [Finsupp.mem_support_iff, not_not] using hi : s i = 0)

theorem squarefree_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2)
    (hs : ∀ i, s i ≤ 1) : monomial s c = c • xMon s.support := by
  rw [xMon_eq_monomial, smul_monomial, smul_eq_mul, mul_one,
    ← squarefree_eq_indicator s hs]

theorem squarefree_sum {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s.sum (fun _ e => e) = s.support.card := by
  have heq := squarefree_monomial s (1 : ZMod 2) hs
  have hd := congrArg MvPolynomial.totalDegree heq
  simpa only [totalDegree_monomial _ one_ne_zero, one_smul, xMon_totalDegree] using hd

noncomputable def monomialSpan {V : Type*} (P : Finset V → Prop) :
    Submodule (ZMod 2) (MvPolynomial V (ZMod 2)) :=
  Submodule.span (ZMod 2) {p | ∃ S : Finset V, P S ∧ p = xMon S}

theorem mem_monomialSpan_iff {V : Type*} (P : Finset V → Prop)
    (p : MvPolynomial V (ZMod 2)) : p ∈ monomialSpan P ↔
      IsMultilinear p ∧ ∀ s ∈ p.support, P s.support := by
  classical
  let M := restrictSupport (ZMod 2) {s : V →₀ ℕ | (∀ i, s i ≤ 1) ∧ P s.support}
  have heq : monomialSpan P = M := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro q ⟨S, hS, rfl⟩
      rw [xMon_eq_monomial]
      apply (monomial_mem_restrictSupport (ZMod 2)).mpr
      left
      refine ⟨?_, ?_⟩
      · intro i
        simp only [Finsupp.indicator_apply]
        split_ifs <;> omega
      · simpa only [indicator_support] using hS
    · intro q hq
      have hq' : ∀ s ∈ q.support, (∀ i, s i ≤ 1) ∧ P s.support := hq
      rw [q.as_sum]
      apply Submodule.sum_mem
      intro s hs
      obtain ⟨hml, hP⟩ := hq' s hs
      rw [squarefree_monomial s _ hml]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s.support, hP, rfl⟩)
  rw [heq, mem_restrictSupport_iff (ZMod 2)]
  constructor
  · intro hp
    exact ⟨fun s hs i => (hp hs).1 i, fun s hs => (hp hs).2⟩
  · rintro ⟨hml, hP⟩ s hs
    exact ⟨hml s hs, hP s hs⟩

theorem mem_light_iff {V : Type*} (m : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ monomialSpan (fun S : Finset V => S.card ≤ m) ↔
      IsMultilinear p ∧ p.totalDegree ≤ m := by
  rw [mem_monomialSpan_iff]
  constructor
  · rintro ⟨hp, hP⟩
    refine ⟨hp, Finset.sup_le fun s hs => ?_⟩
    rw [squarefree_sum s (hp s hs)]
    exact hP s hs
  · rintro ⟨hp, hd⟩
    refine ⟨hp, fun s hs => ?_⟩
    rw [← squarefree_sum s (hp s hs)]
    exact (le_totalDegree hs).trans hd

theorem point_interpolation {V : Type} [Fintype V] [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) :
    p = ∑ S : Finset V, eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p • pointPoly S := by
  apply multilinear_ext hp
    (multilinear_sum _ _ (fun S _ =>
      (mem_restrictDegree V _ 1).mp ((restrictDegree V (ZMod 2) 1).smul_mem _
        ((mem_restrictDegree V _ 1).mpr (pointPoly_multilinear S)))))
  intro x
  simp only [map_sum, smul_eval, pointPoly_eval]
  have heq (S : Finset V) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro h; rw [h, ones_of_point]
    · intro h; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp
  have hx : (fun i => if x i = 1 then (1 : ZMod 2) else 0) = x := by
    funext i
    rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]
  rw [hx]

end AC02Frege.P2MBooleanBasis
end

section
-- Inlined Solutions.P2MBooleanDegreeSpaces

open MvPolynomial AC02Frege AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MBooleanDegreeSpaces

theorem mem_Ble_iff {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ Ble V D ↔ IsMultilinear p ∧ p.totalDegree ≤ D := by
  have he : Ble V D = monomialSpan (fun A : Finset V => A.card ≤ D) := by
    unfold Ble monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨A,hA,rfl⟩; exact ⟨A,hA,rfl⟩
    · rintro ⟨A,hA,rfl⟩; exact ⟨A,hA,rfl⟩
  rw [he,mem_light_iff]

end SemAC02.P2MBooleanDegreeSpaces
end

section
-- Inlined Solutions.P2MBooleanVariableEquivalence

set_option maxHeartbeats 2000000

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MBooleanVariableEquivalence

theorem multilinear_rename {V W : Type} (e : V ≃ W) {p : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) : IsMultilinear (rename e p) := by
  classical
  intro s hs w
  rw [support_rename_of_injective e.injective] at hs
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
  simpa only [Finsupp.mapDomain_equiv_apply] using hp t ht (e.symm w)

theorem ml_rename {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (p : MvPolynomial V (ZMod 2)) : rename e (ML p) = ML (rename e p) := by
  apply multilinear_ext (multilinear_rename e (ml_multilinear p)) (ml_multilinear _)
  intro x
  simp only [eval_rename,eval_ml]

theorem rename_mem_Ble {V W : Type} (e : V ≃ W) {k : ℕ} {p : MvPolynomial V (ZMod 2)}
    (hp : p ∈ Ble V k) : rename e p ∈ Ble W k := by
  rcases P2MBooleanDegreeSpaces.mem_Ble_iff k p |>.mp hp with ⟨hml,hdeg⟩
  exact (P2MBooleanDegreeSpaces.mem_Ble_iff k _).mpr
    ⟨multilinear_rename e hml,(totalDegree_rename_le e p).trans hdeg⟩

theorem map_Ble {V W : Type} (e : V ≃ W) (k : ℕ) :
    (Ble V k).map (rename e).toLinearMap = Ble W k := by
  apply le_antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact rename_mem_Ble e hp
  · intro p hp
    refine ⟨rename e.symm p,rename_mem_Ble e.symm hp,?_⟩
    exact (renameEquiv (ZMod 2) e).apply_symm_apply p

theorem mulML_rename {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f p : MvPolynomial V (ZMod 2)) : rename e (mulML f p) = mulML (rename e f) (rename e p) := by
  simp only [mulML,LinearMap.comp_apply,LinearMap.mulLeft_apply]
  rw [ml_rename,map_mul]

theorem rename_mem_multSpace {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) {p : MvPolynomial V (ZMod 2)}
    (hp : p ∈ multSpace f k) : rename e p ∈ multSpace (rename e f) k := by
  obtain ⟨q,hq,rfl⟩ := hp
  exact ⟨rename e q,rename_mem_Ble e hq,(mulML_rename e f q).symm⟩

theorem map_multSpace {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) :
    (multSpace f k).map (rename e).toLinearMap = multSpace (rename e f) k := by
  apply le_antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact rename_mem_multSpace e f k hp
  · intro p hp
    have hf : rename e.symm (rename e f) = f := (renameEquiv (ZMod 2) e).symm_apply_apply f
    refine ⟨rename e.symm p,?_,?_⟩
    · have hh := rename_mem_multSpace e.symm (rename e f) k hp
      rw [hf] at hh
      exact hh
    · exact (renameEquiv (ZMod 2) e).apply_symm_apply p

theorem finrank_map {V W : Type} (e : V ≃ W)
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) :
    Module.finrank (ZMod 2) (U.map (rename e).toLinearMap) = Module.finrank (ZMod 2) U := by
  exact (Submodule.equivMapOfInjective (rename e).toLinearMap
    (renameEquiv (ZMod 2) e).injective U).finrank_eq.symm

noncomputable def spaceEquiv {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) :
    multSpace f k ≃ₗ[ZMod 2] multSpace (rename e f) k where
  toFun u := ⟨rename e u.val,rename_mem_multSpace e f k u.property⟩
  invFun u := ⟨rename e.symm u.val,by
    have h := rename_mem_multSpace e.symm (rename e f) k u.property
    have hf : rename e.symm (rename e f) = f := (renameEquiv (ZMod 2) e).symm_apply_apply f
    rw [hf] at h
    exact h⟩
  left_inv u := Subtype.ext ((renameEquiv (ZMod 2) e).symm_apply_apply u.val)
  right_inv u := Subtype.ext ((renameEquiv (ZMod 2) e).apply_symm_apply u.val)
  map_add' u v := Subtype.ext (map_add (rename e) u.val v.val)
  map_smul' a u := Subtype.ext ((rename e).toLinearMap.map_smul a u.val)

@[simp] theorem spaceEquiv_val {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) (u : multSpace f k) :
    (spaceEquiv e f k u).val = rename e u.val := rfl

@[simp] theorem spaceEquiv_symm_val {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) (u : multSpace (rename e f) k) :
    ((spaceEquiv e f k).symm u).val = rename e.symm u.val := rfl

end SemAC02.P2MBooleanVariableEquivalence
end

section
-- Inlined Solutions.P2MRelativeReductionVariableEquivalence

set_option maxHeartbeats 2000000

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MRelativeReductionVariableEquivalence

open P2MBooleanVariableEquivalence

theorem hasNonzero_rename {V W : Type} [Finite V] [Finite W] (e : V ≃ W)
    {S : Set (MvPolynomial V (ZMod 2))} {f : MvPolynomial V (ZMod 2)} {k : ℕ}
    (h : HasNonzeroRelPseudoRed S f k) :
    HasNonzeroRelPseudoRed (rename e '' S) (rename e f) k := by
  obtain ⟨T,hT,hM,R,hR,hax,hvar⟩ := h
  let ρ := spaceEquiv e f k
  let R' := R.comp ρ.symm.toLinearMap
  refine ⟨T,hT,hM,R',?_,?_,?_⟩
  · intro hz
    apply hR
    ext u
    have hzero := congrArg (fun L : multSpace (rename e f) k →ₗ[ZMod 2] T => L (ρ u)) hz
    simpa only [R',LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply,LinearMap.zero_apply] using hzero
  · rintro a' ⟨a,ha,rfl⟩ hmem
    let u : multSpace (rename e f) k := ⟨mulML (rename e f) (rename e a),hmem⟩
    have hv : (ρ.symm u).val = mulML f a := by
      change rename e.symm (mulML (rename e f) (rename e a)) = mulML f a
      rw [← mulML_rename]
      exact (renameEquiv (ZMod 2) e).symm_apply_apply _
    have hmem' : mulML f a ∈ multSpace f k := hv ▸ (ρ.symm u).property
    have hz := hax a ha hmem'
    change R (ρ.symm u) = 0
    convert hz using 1
    apply congrArg R
    exact Subtype.ext hv
  · intro i u hmem hu
    let v : multSpace (rename e f) k := ⟨ML (X i * u.val),hmem⟩
    have hv : (ρ.symm v).val = ML (X (e.symm i)*(ρ.symm u).val) := by
      change rename e.symm (ML (X i*u.val)) = ML (X (e.symm i)*rename e.symm u.val)
      rw [ml_rename,map_mul,rename_X]
    have hmem' : ML (X (e.symm i)*(ρ.symm u).val) ∈ multSpace f k := hv ▸ (ρ.symm v).property
    have hz := hvar (e.symm i) (ρ.symm u) hmem' hu
    change R (ρ.symm v) = 0
    convert hz using 1
    apply congrArg R
    exact Subtype.ext hv

end SemAC02.P2MRelativeReductionVariableEquivalence
end

section
-- Inlined Solutions.P2MCircuitSemantics

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MCircuitSemantics

theorem arithmetic_and (bs : List Bool) :
    1 + (bs.map (fun b => 1 + (if b then 0 else 1 : ZMod 2))).prod =
      if bs.all id then 0 else 1 := by
  induction bs with
  | nil => simp [CharTwo.add_self_eq_zero]
  | cons b bs ih =>
    cases b <;> simp only [List.map_cons, List.prod_cons, List.all_cons, id_eq,
      Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      CharTwo.add_self_eq_zero, zero_mul, add_zero, one_mul] at *
    exact ih

theorem arithmetic_or (bs : List Bool) :
    (bs.map (fun b : Bool => (if b then 0 else 1 : ZMod 2))).prod =
      if bs.any id then 0 else 1 := by
  induction bs with
  | nil => simp
  | cons b bs ih => cases b <;> simp [ih]

theorem arithmetic_xor (bs : List Bool) :
    1 + (bs.map (fun b => 1 + (if b then 0 else 1 : ZMod 2))).sum =
      if bs.foldr Bool.xor false then 0 else 1 := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    cases h : bs.foldr Bool.xor false <;> cases b <;>
      simp [h, List.map_cons, List.sum_cons, CharTwo.add_self_eq_zero] at ih ⊢ <;> simpa only [← add_assoc, CharTwo.add_self_eq_zero, zero_add] using ih

theorem arithRaw_eval {V : Type} (A : Circ V) (X : V → Bool) :
    eval (toF2 X) (arithRaw A) = if A.eval X then 0 else 1 := by
  cases A with
  | const b => cases b <;> simp [arithRaw, Circ.eval]
  | lit v b => cases b <;> cases h : X v <;> simp [arithRaw, Circ.eval, toF2, h, CharTwo.add_self_eq_zero]
  | and cs =>
    simp only [arithRaw, map_add, map_one, map_list_prod, List.map_map, Function.comp_def]
    have he : cs.map (fun c => 1 + eval (toF2 X) (arithRaw c)) =
        (cs.map (fun c => c.eval X)).map (fun b => 1 + (if b then 0 else 1 : ZMod 2)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro c hc
      rw [arithRaw_eval c X]
      rfl
    rw [he, arithmetic_and]
    simp only [Circ.eval]
  | or cs =>
    simp only [arithRaw, map_list_prod, List.map_map, Function.comp_def]
    have he : cs.map (fun c => eval (toF2 X) (arithRaw c)) =
        (cs.map (fun c => c.eval X)).map (fun b : Bool => (if b then 0 else 1 : ZMod 2)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro c hc
      rw [arithRaw_eval c X]
      rfl
    rw [he, arithmetic_or]
    simp only [Circ.eval]
  | xor cs =>
    simp only [arithRaw, map_add, map_one, map_list_sum, List.map_map, Function.comp_def]
    have he : cs.map (fun c => 1 + eval (toF2 X) (arithRaw c)) =
        (cs.map (fun c => c.eval X)).map (fun b => 1 + (if b then 0 else 1 : ZMod 2)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro c hc
      rw [arithRaw_eval c X]
      rfl
    rw [he, arithmetic_xor]
    simp only [Circ.eval]
termination_by A
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

@[simp] theorem arith_eval {V : Type} (A : Circ V) (X : V → Bool) :
    eval (toF2 X) (arith A) = if A.eval X then 0 else 1 := by
  rw [arith, eval_ml, arithRaw_eval]

theorem eval_rename {V W : Type} (A : Circ V) (f : V → W) (X : W → Bool) :
    (A.rename f).eval X = A.eval (fun v => X (f v)) := by
  cases A with
  | const b => simp [Circ.rename, Circ.flip, Circ.eval]
  | lit v b => simp [Circ.rename, Circ.eval]
  | and cs =>
    simp only [Circ.rename, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename c f X
  | or cs =>
    simp only [Circ.rename, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename c f X
  | xor cs =>
    simp only [Circ.rename, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename c f X

termination_by A
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem eval_flip {V : Type} (A : Circ V) (X : V → Bool) :
    A.flip.eval X = A.eval (fun v => !X v) := by
  cases A with
  | const b => simp [Circ.rename, Circ.flip, Circ.eval]
  | lit v b => cases b <;> simp [Circ.flip, Circ.eval]
  | and cs =>
    simp only [Circ.flip, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_flip c X
  | or cs =>
    simp only [Circ.flip, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_flip c X
  | xor cs =>
    simp only [Circ.flip, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_flip c X

termination_by A
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem eval_orChildren {V : Type} (A : Circ V) (X : V → Bool) :
    (A.orChildren.map (fun c => c.eval X)).any id = A.eval X := by
  cases A <;> simp [Circ.orChildren, Circ.eval]

theorem eval_andChildren {V : Type} (A : Circ V) (X : V → Bool) :
    (A.andChildren.map (fun c => c.eval X)).all id = A.eval X := by
  cases A <;> simp [Circ.andChildren, Circ.eval]

theorem eval_liftAxiom {n m : ℕ} (g : Circ (Fin m))
    (C : LiftSAParity.Clause (Fin n))
    (α : Fin n × Bool → Fin g.andChildren.length) (X : Fin n × Fin m → Bool) :
    (liftAxiom g C α).eval X = true ↔
      ∃ l ∈ C, (gadgetH g l.2 (α l)).eval (fun j => X (l.1, j)) = true := by
  classical
  simp only [liftAxiom, Circ.eval, List.map_flatMap, List.any_flatMap]
  simp only [List.map_map, Function.comp_def, eval_rename]
  simp only [eval_orChildren, List.any_eq_true, Finset.mem_toList]


end SemAC02.P2MCircuitSemantics
end

section
-- Inlined Solutions.P2MFiniteVariableSizeBound

set_option maxHeartbeats 2000000

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MFiniteVariableSizeBound

theorem toF2_surjective {V : Type} (x : V → ZMod 2) : ∃ X : V → Bool, toF2 X = x := by
  refine ⟨fun v => decide (x v = 1),?_⟩
  funext v
  rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (x v) with h | h <;> simp [toF2,h]

theorem arith_rename {V W : Type} [Finite V] [Finite W] (e : V ≃ W) (A : Circ V) :
    arith (A.rename e) = rename e (arith A) := by
  have hleft : IsMultilinear (arith (A.rename e)) := by
    simpa only [arith] using ml_multilinear (arithRaw (A.rename e))
  have hright : IsMultilinear (rename e (arith A)) :=
    P2MBooleanVariableEquivalence.multilinear_rename e (by simpa only [arith] using ml_multilinear (arithRaw A))
  apply multilinear_ext hleft hright
  intro x
  obtain ⟨X,hX⟩ := toF2_surjective x
  rw [← hX]
  rw [P2MCircuitSemantics.arith_eval,P2MCircuitRenaming.eval_rename,MvPolynomial.eval_rename]
  have hx : toF2 X ∘ e = toF2 (fun v => X (e v)) := by
    funext v
    simp only [toF2,Function.comp_apply]
  rw [hx,P2MCircuitSemantics.arith_eval]
  simp only [Function.comp_def]

theorem arith_image {V W : Type} [Finite V] [Finite W] (e : V ≃ W) (F : Set (Circ V)) :
    arith '' (Circ.rename e '' F) = rename e '' (arith '' F) := by
  rw [Set.image_image,Set.image_image]
  exact congrArg (fun f : Circ V → MvPolynomial W (ZMod 2) => f '' F)
    (funext (fun A => arith_rename e A))

/-- Corollary 4.18 for any finite variable type, preserving the exact size and dimension
quantities. This allows its use on the block-product variables in Section 8. -/
theorem corollary_size_bound {V : Type} [Fintype V] (F : Set (Circ V))
    (d r R : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hR : 1 ≤ R)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε ≤ 1/256)
    (hn : 16/ε^2 ≤ (Fintype.card V : ℝ))
    (hrn : (r : ℝ)^(d-1) ≤ ε*Fintype.card V/2)
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (hU : U ≤ Ble V ⌊(1/2-ε)*(Fintype.card V : ℝ)⌋₊)
    (hred : ∀ f ∈ U, f ≠ 0 → HasNonzeroRelPseudoRed (arith '' F) f (3*(R*r^(d-1))))
    (π : List (Circ V)) (hπ : IsSemRefutation d F π) :
    (Module.finrank (ZMod 2) U : ℝ)/(Hn (Fintype.card V) ⌊(1/2-ε)*(Fintype.card V : ℝ)⌋₊ : ℝ)*
      Real.exp (1/2*min ((r : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-2))))
        ((R : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-1))))) ≤ (proofSize π : ℝ) := by
  let e := Fintype.equivFin V
  let F' := Circ.rename e '' F
  let U' := U.map (rename e).toLinearMap
  have hU' : U' ≤ Ble (Fin (Fintype.card V)) ⌊(1/2-ε)*(Fintype.card V : ℝ)⌋₊ := by
    rw [← P2MBooleanVariableEquivalence.map_Ble e]
    exact Submodule.map_mono hU
  have hred' : ∀ f ∈ U', f ≠ 0 → HasNonzeroRelPseudoRed (arith '' F') f (3*(R*r^(d-1))) := by
    rintro f ⟨p,hp,rfl⟩ hne
    have hpne : p ≠ 0 := by
      intro hz
      apply hne
      simp only [hz,AlgHom.toLinearMap_apply,map_zero]
    have h := P2MRelativeReductionVariableEquivalence.hasNonzero_rename e (hred p hp hpne)
    rw [← arith_image e F] at h
    exact h
  have h := corollary_4_18_frege_size_bound F' d r R hd hr hR ε hε₀ hε hn hrn U' hU' hred'
    (π.map (Circ.rename e)) (P2MCircuitVariableEquivalence.refutation_rename e hπ)
  have hdim : Module.finrank (ZMod 2) U' = Module.finrank (ZMod 2) U := P2MBooleanVariableEquivalence.finrank_map e U
  have hsize := P2MCircuitVariableEquivalence.proofSize_rename e π
  rw [hdim,hsize] at h
  exact h

end SemAC02.P2MFiniteVariableSizeBound
end

section
-- Inlined Solutions.PCOperations

open MvPolynomial

namespace AC02Frege.P2MSupport

theorem derivation_append {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K))
    {π ρ : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π)
    (hρ : PCNonBool.IsDerivation red P ρ) :
    PCNonBool.IsDerivation red P (π ++ ρ) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left
      simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    have hk' : k < ρ.length := by simp only [List.length_append] at hk; omega
    have hget (t : ℕ) (ht : t < ρ.length) :
        (π ++ ρ)[π.length + t]'(by simp only [List.length_append]; omega) = ρ[t] := by
      rw [List.getElem_append_right (Nat.le_add_right π.length t)]
      simp only [Nat.add_sub_cancel_left]
    rcases hρ k hk' with ha | hc | hm
    · left
      obtain ⟨a, ha, c, hac⟩ := ha
      exact ⟨a, ha, c, (hget k hk').trans hac⟩
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨π.length + i, π.length + j, by omega, by omega, a, b, ?_⟩
      rw [hget k hk', hget i (hi.trans hk'), hget j (hj.trans hk')]
      exact hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨π.length + i, by omega, v, ?_⟩
      rw [hget k hk', hget i (hi.trans hk')]
      exact hiv

theorem derivation_snoc {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K)) {π : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π) (p : MvPolynomial σ K)
    (hp :
      (∃ a ∈ P, ∃ c : K, p = c • red a) ∨
      (∃ (i j : ℕ) (hi : i < π.length) (hj : j < π.length) (a b : K),
        p = a • π[i] + b • π[j]) ∨
      (∃ (i : ℕ) (hi : i < π.length) (v : σ), p = red (X v * π[i]))) :
    PCNonBool.IsDerivation red P (π ++ [p]) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left; simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · have heq : k = π.length := by simp only [List.length_append, List.length_singleton] at hk; omega
    subst k
    have hlast : (π ++ [p])[π.length] = p := by
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
    rcases hp with ha | hc | hm
    · left; simpa only [hlast] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [hlast, List.getElem_append_left hi, List.getElem_append_left hj] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [hlast, List.getElem_append_left hi] using hiv

theorem pc_zero {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ) :
    PCDerivable F D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {F : LiftSAParity.CNF (Fin n)} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) (c : ZMod 2) :
    PCDerivable F D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero F D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : PCDerivable F D p) (hq : PCDerivable F D q) :
    PCDerivable F D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show PCDerivable F D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    PCDerivable F D (p * X v) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [zero_mul]; exact pc_zero F D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [p * X v], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by simp only [hpi, LinearMap.id_apply, mul_comm]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = p * X v := List.mem_singleton.mp hq
      subst q
      exact (totalDegree_mul p (X v)).trans (by simpa only [totalDegree_X] using hdeg)

theorem pc_axiom {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ pcAxioms F)
    (hdeg : p.totalDegree ≤ D) : PCDerivable F D p := by
  refine Or.inr ⟨[p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

end AC02Frege.P2MSupport
end

section
-- Inlined Solutions.P2MBooleanFlip

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation AC02Frege.P2MBooleanBasis

namespace AC02Frege.P2MBooleanFlip

theorem ml_totalDegree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (ML p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply (totalDegree_monomial_le _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  simp only [Finsupp.sum, sqfree_support]
  apply Finset.sum_le_sum
  intro i _
  simp only [sqfree, Finsupp.mapRange_apply]
  exact min_le_left _ _

theorem bind_linear_totalDegree_le {V W : Type*} (f : V → MvPolynomial W (ZMod 2))
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial V (ZMod 2)) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, bind₁_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply le_trans (totalDegree_mul _ _)
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))

noncomputable def flip {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    MvPolynomial V (ZMod 2) := ML (bind₁ (fun i => 1 + X i) p)

theorem flip_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (flip p) := ml_multilinear _

theorem flip_degree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (flip p).totalDegree ≤ p.totalDegree := by
  apply (ml_totalDegree_le _).trans
  apply bind_linear_totalDegree_le
  intro i
  exact (totalDegree_add _ _).trans (by simp)

theorem flip_eval {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (flip p) = eval (fun i => 1 + x i) p := by
  rw [flip, eval_ml]
  simp only [eval, eval₂Hom_bind₁, map_add, map_one, eval₂Hom_X']

theorem flip_involution {V : Type} [Finite V] (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : flip (flip p) = p := by
  apply multilinear_ext (flip_multilinear _) hp
  intro x
  simp only [flip_eval, CharTwo.add_cancel_left]

end AC02Frege.P2MBooleanFlip
end

section
-- Inlined Solutions.P2MBooleanPC

open MvPolynomial AC02Frege
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MBooleanPC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q.totalDegree ≤ D) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Derivable P D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) (c : ZMod 2) :
    Derivable P D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero P D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : Derivable P D p) (hq : Derivable P D q) :
    Derivable P D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show Derivable P D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    Derivable P D (ML (X v * p)) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [mul_zero, map_zero]; exact pc_zero P D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = ML (X v * p) := List.mem_singleton.mp hq
      subst q
      exact (ml_totalDegree_le _).trans ((totalDegree_mul (X v) p).trans (by simpa only [totalDegree_X, Nat.add_comm] using hdeg))

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P)
    (hdeg : (ML p).totalDegree ≤ D) : Derivable P D (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

theorem pc_mono {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D E : ℕ}
    (hDE : D ≤ E) {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) :
    Derivable P E p := by
  rcases hp with h | ⟨π, hπ, hdeg, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨π, hπ, fun q hq => (hdeg q hq).trans hDE, hp⟩

noncomputable def consequenceSpace {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) where
  carrier := {p | Derivable P D p}
  zero_mem' := pc_zero P D
  add_mem' := pc_add P D
  smul_mem' := fun a _ hp => pc_smul P D hp a

end SemAC02.P2MBooleanPC
end

section
-- Inlined Solutions.P2MRelativePCFinite

open MvPolynomial AC02Frege SemAC02
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePCFinite

def Derivable {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (p : MvPolynomial V (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial V (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q ∈ U) ∧ p ∈ π

theorem pc_zero {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) : Derivable P U 0 := Or.inl rfl

theorem pc_mem {V : Type} {P : Set (MvPolynomial V (ZMod 2))}
    {U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))}
    {p : MvPolynomial V (ZMod 2)} (hp : Derivable P U p) : p ∈ U := by
  rcases hp with rfl | ⟨π,_,hmem,hp⟩
  · exact U.zero_mem
  · exact hmem p hp

theorem pc_smul {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    {p : MvPolynomial V (ZMod 2)} (hp : Derivable P U p) (c : ZMod 2) :
    Derivable P U (c • p) := by
  rcases hp with rfl | ⟨π,hπ,hmem,hp⟩
  · simp only [smul_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; left
    exact ⟨i,i,hi,hi,c,0,by simp only [hpi,zero_smul,add_zero]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hmem q hq
    · have he : q = c • p := List.mem_singleton.mp hq
      rw [he]
      exact U.smul_mem c (hmem p hp)

theorem pc_add {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    {p q : MvPolynomial V (ZMod 2)} (hp : Derivable P U p) (hq : Derivable P U q) :
    Derivable P U (p+q) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ,hρ,hρmem,hq⟩
  · simpa only [add_zero] using (show Derivable P U p from Or.inr ⟨π,hπ,hπmem,hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j,hj,hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p+q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i,j,hi,hj,1,1,by simp only [hpi,hqj,one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπmem r hr
      · exact hρmem r hr
    · have he : r = p+q := List.mem_singleton.mp hr
      rw [he]
      exact U.add_mem (hπmem p hp) (hρmem q hq)

theorem pc_mul_X {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    {p : MvPolynomial V (ZMod 2)} (hp : Derivable P U p) (v : V)
    (hmem : ML (X v * p) ∈ U) : Derivable P U (ML (X v * p)) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simp only [mul_zero,map_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i,hi,v,by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπmem q hq
    · rwa [List.mem_singleton.mp hq]

theorem pc_axiom {V : Type} (P : Set (MvPolynomial V (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (p : MvPolynomial V (ZMod 2)) (hp : p ∈ P) (hmem : ML p ∈ U) :
    Derivable P U (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hmem, by simp⟩
  intro k hk
  have he : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p,hp,1,by simp⟩

end SemAC02.P2MRelativePCFinite
end

section
-- Inlined Solutions.P2MNaiveRelativeReduction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MNaiveRelativeReduction

theorem derivable_mem_span {V : Type} (S : Set (MvPolynomial V (ZMod 2)))
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) (p : MvPolynomial V (ZMod 2))
    (hp : P2MRelativePCFinite.Derivable (mulML f '' S) (multSpace f k) p) :
    p ∈ Submodule.span (ZMod 2) {u | RelDerivable S f k u} := by
  rcases hp with rfl | ⟨π,hπ,hspace,hp⟩
  · exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨π,hπ,hspace,hp⟩

theorem span_derivable {V : Type} (S : Set (MvPolynomial V (ZMod 2)))
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) (p : MvPolynomial V (ZMod 2))
    (hp : p ∈ Submodule.span (ZMod 2) {u | RelDerivable S f k u}) :
    P2MRelativePCFinite.Derivable (mulML f '' S) (multSpace f k) p := by
  induction hp using Submodule.span_induction with
  | mem p hp => exact Or.inr hp
  | zero => exact P2MRelativePCFinite.pc_zero _ _
  | add p q hp hq ihp ihq => exact P2MRelativePCFinite.pc_add _ _ ihp ihq
  | smul a p hp ih => exact P2MRelativePCFinite.pc_smul _ _ ih a

theorem isRelPseudoRed {V : Type} (S : Set (MvPolynomial V (ZMod 2)))
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) :
    IsRelPseudoRed S f k (naiveRelPR S f k) := by
  constructor
  · intro a ha hmem
    rw [naiveRelPR,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    change mulML f a ∈ Submodule.span (ZMod 2) {u | RelDerivable S f k u}
    have he : ML (mulML f a) = mulML f a := ml_idempotent _
    have hd := P2MRelativePCFinite.pc_axiom (mulML f '' S) (multSpace f k)
      (mulML f a) ⟨a,ha,rfl⟩ (by rw [he]; exact hmem)
    rw [he] at hd
    exact derivable_mem_span S f k _ hd
  · intro i u hmem hu
    rw [naiveRelPR,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at hu ⊢
    change u.val ∈ Submodule.span (ZMod 2) {w | RelDerivable S f k w} at hu
    change ML (X i*u.val) ∈ Submodule.span (ZMod 2) {w | RelDerivable S f k w}
    exact derivable_mem_span S f k _
      (P2MRelativePCFinite.pc_mul_X _ _ (span_derivable S f k _ hu) i hmem)

theorem hasNonzero {V : Type} (S : Set (MvPolynomial V (ZMod 2)))
    (f : MvPolynomial V (ZMod 2)) (k : ℕ) (h : naiveRelPR S f k ≠ 0) :
    HasNonzeroRelPseudoRed S f k :=
  ⟨multSpace f k ⧸ relDerivSpace S f k,inferInstance,inferInstance,
    naiveRelPR S f k,h,isRelPseudoRed S f k⟩

end SemAC02.P2MNaiveRelativeReduction
end

section
-- Inlined Solutions.P2MLiftedNumericLowerBound

set_option maxHeartbeats 2000000

open MvPolynomial AC02Frege

namespace SemAC02.P2MLiftedNumericLowerBound

theorem multiplier_le_Ble {n m : ℕ} (g : (Fin m → Bool) → Bool) (k : ℕ) :
    multiplierSpace g n k ≤ Ble (Fin n × Fin m) k := by
  apply Submodule.span_mono
  rintro p ⟨A,⟨hcard,hln⟩,rfl⟩
  exact ⟨A,hcard,rfl⟩

/-- The finite-parameter lower bound used in Theorem 8.1. No asymptotic assumptions are
hidden: the PC-degree gap, approximation budget, and multiplier density are explicit. -/
theorem lower_bound {n m d Δ r R : ℕ} (hd : 2 ≤ d) {g : Circ (Fin m)} (hg : IsGadget d g)
    (F : LiftSAParity.CNF (Fin n)) (hF : ¬LiftSAParity.Satisfiable F) (hΔ : PCDegreeAtLeast F Δ)
    (hr : 1 ≤ r) (hR : 1 ≤ R) (hgap : 3*(R*r^(d-1))+1 < Δ)
    (ε : ℝ) (hεpos : 0 < ε) (hεmax : ε ≤ 1/256)
    (hvars : 16/ε^2 ≤ ((n*m : ℕ) : ℝ))
    (hbudget : (r : ℝ)^(d-1) ≤ ε*((n*m : ℕ) : ℝ)/2)
    (α : ℝ)
    (hdim : α ≤
      (Module.finrank (ZMod 2) (multiplierSpace (fun X => g.eval X) n
        ⌊(1/2-ε)*((n*m : ℕ) : ℝ)⌋₊) : ℝ)/
        (Hn (n*m) ⌊(1/2-ε)*((n*m : ℕ) : ℝ)⌋₊ : ℝ))
    (π : List (Circ (Fin n × Fin m)))
    (hπ : IsSemRefutation d (lift g F : Set (Circ (Fin n × Fin m))) π) :
    α*Real.exp (1/2*min ((r : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-2))))
      ((R : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-1))))) ≤ (proofSize π : ℝ) := by
  let k := ⌊(1/2-ε)*((n*m : ℕ) : ℝ)⌋₊
  let U := multiplierSpace (fun X => g.eval X) n k
  have hred : ∀ f ∈ U, f ≠ 0 → HasNonzeroRelPseudoRed
      (arith '' (lift g F : Set (Circ (Fin n × Fin m)))) f (3*(R*r^(d-1))) := by
    intro f hf hne
    apply P2MNaiveRelativeReduction.hasNonzero
    exact (lemma_8_4_degree_transfer hd g hg F hF k f hf hne _).2 Δ hΔ hgap
  have hvars' : 16/ε^2 ≤ (Fintype.card (Fin n × Fin m) : ℝ) := by simpa using hvars
  have hbudget' : (r : ℝ)^(d-1) ≤ ε*Fintype.card (Fin n × Fin m)/2 := by simpa using hbudget
  have hU : U ≤ Ble (Fin n × Fin m) ⌊(1/2-ε)*(Fintype.card (Fin n × Fin m) : ℝ)⌋₊ := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using multiplier_le_Ble (fun X => g.eval X) k
  have h := P2MFiniteVariableSizeBound.corollary_size_bound (lift g F : Set (Circ (Fin n × Fin m)))
    d r R hd hr hR ε hεpos hεmax hvars' hbudget' U hU hred π hπ
  simp only [Fintype.card_prod,Fintype.card_fin] at h
  exact (mul_le_mul_of_nonneg_right hdim (Real.exp_pos _).le).trans h

end SemAC02.P2MLiftedNumericLowerBound
end

section
-- Inlined Solutions.P2MMonotoneCircuitDual

set_option maxHeartbeats 1000000

namespace SemAC02.P2MMonotoneCircuitDual

def dual {V : Type} : Circ V → Circ V
  | .const b => .const (!b)
  | .lit v b => .lit v b
  | .and cs => .or (cs.map dual)
  | .or cs => .and (cs.map dual)
  | .xor cs => .xor (cs.map dual)

theorem dual_dual {V : Type} (C : Circ V) : dual (dual C) = C := by
  cases C with
  | const b => simp [dual]
  | lit v b => simp [dual,Circ.depth,Circ.treeSize]
  | and cs =>
    simp only [dual,List.map_map]
    congr 1
    calc
      cs.map (dual ∘ dual) = cs.map (fun c => c) := by
        apply List.map_congr_left
        intro c hc
        exact dual_dual c
      _ = cs := List.map_id' _
  | or cs =>
    simp only [dual,List.map_map]
    congr 1
    calc
      cs.map (dual ∘ dual) = cs.map (fun c => c) := by
        apply List.map_congr_left
        intro c hc
        exact dual_dual c
      _ = cs := List.map_id' _
  | xor cs =>
    simp only [dual,List.map_map]
    congr 1
    calc
      cs.map (dual ∘ dual) = cs.map (fun c => c) := by
        apply List.map_congr_left
        intro c hc
        exact dual_dual c
      _ = cs := List.map_id' _
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem dual_injective {V : Type} : Function.Injective (@dual V) :=
  Function.LeftInverse.injective dual_dual

@[simp] theorem isAnd_dual {V : Type} (C : Circ V) : (dual C).isAnd = C.isOr := by cases C <;> simp [dual,Circ.isAnd,Circ.isOr,Circ.isXor]
@[simp] theorem isOr_dual {V : Type} (C : Circ V) : (dual C).isOr = C.isAnd := by cases C <;> simp [dual,Circ.isAnd,Circ.isOr,Circ.isXor]
@[simp] theorem isXor_dual {V : Type} (C : Circ V) : (dual C).isXor = C.isXor := by cases C <;> simp [dual,Circ.isAnd,Circ.isOr,Circ.isXor]

theorem monotone_dual {V : Type} {C : Circ V} (hC : IsMonotoneCirc C) : IsMonotoneCirc (dual C) := by
  induction hC with
  | const b => simpa only [dual] using IsMonotoneCirc.const (V := V) (!b)
  | lit v => simpa only [dual] using IsMonotoneCirc.lit v
  | and cs hcs ih =>
    rw [dual]
    apply IsMonotoneCirc.or
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
    exact ih c' hc'
  | or cs hcs ih =>
    rw [dual]
    apply IsMonotoneCirc.and
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
    exact ih c' hc'

theorem reduced_dual {V : Type} {C : Circ V} (hC : IsReduced C) : IsReduced (dual C) := by
  induction hC with
  | const b => simpa only [dual] using IsReduced.const (V := V) (!b)
  | lit v b => simpa only [dual] using IsReduced.lit v b
  | and cs hn htype hred ih =>
    rw [dual]
    apply IsReduced.or
    · exact hn.map dual_injective
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isOr_dual] using htype c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
  | or cs hn htype hred ih =>
    rw [dual]
    apply IsReduced.and
    · exact hn.map dual_injective
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isAnd_dual] using htype c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
  | xor cs hn htype hred ih =>
    rw [dual]
    apply IsReduced.xor
    · exact hn.map dual_injective
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isXor_dual] using htype c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'

theorem depth_dual {V : Type} (C : Circ V) : (dual C).depth = C.depth := by
  cases C with
  | const b => simp [dual,Circ.depth,Circ.treeSize,Circ.eval]
  | lit v b => simp [dual,Circ.depth,Circ.treeSize]
  | and cs =>
    have he : cs.map (fun c => (dual c).depth) = cs.map Circ.depth := by
      apply List.map_congr_left
      intro c hc
      exact depth_dual c
    simpa only [dual,Circ.depth,List.map_map,Function.comp_def] using
      congrArg (fun l : List ℕ => 1+l.foldr max 0) he
  | or cs =>
    have he : cs.map (fun c => (dual c).depth) = cs.map Circ.depth := by
      apply List.map_congr_left
      intro c hc
      exact depth_dual c
    simpa only [dual,Circ.depth,List.map_map,Function.comp_def] using
      congrArg (fun l : List ℕ => 1+l.foldr max 0) he
  | xor cs =>
    have he : cs.map (fun c => (dual c).depth) = cs.map Circ.depth := by
      apply List.map_congr_left
      intro c hc
      exact depth_dual c
    simpa only [dual,Circ.depth,List.map_map,Function.comp_def] using
      congrArg (fun l : List ℕ => 1+l.foldr max 0) he
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem size_dual {V : Type} (C : Circ V) : (dual C).treeSize = C.treeSize := by
  cases C with
  | const b => simp [dual,Circ.depth,Circ.treeSize,Circ.eval]
  | lit v b => simp [dual,Circ.depth,Circ.treeSize]
  | and cs =>
    have he : cs.map (fun c => (dual c).treeSize) = cs.map Circ.treeSize := by
      apply List.map_congr_left
      intro c hc
      exact size_dual c
    simpa only [dual,Circ.treeSize,List.map_map,Function.comp_def] using congrArg (fun l : List ℕ => 1+l.sum) he
  | or cs =>
    have he : cs.map (fun c => (dual c).treeSize) = cs.map Circ.treeSize := by
      apply List.map_congr_left
      intro c hc
      exact size_dual c
    simpa only [dual,Circ.treeSize,List.map_map,Function.comp_def] using congrArg (fun l : List ℕ => 1+l.sum) he
  | xor cs =>
    have he : cs.map (fun c => (dual c).treeSize) = cs.map Circ.treeSize := by
      apply List.map_congr_left
      intro c hc
      exact size_dual c
    simpa only [dual,Circ.treeSize,List.map_map,Function.comp_def] using congrArg (fun l : List ℕ => 1+l.sum) he
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem any_not (bs : List Bool) : (bs.map Bool.not).any id = !(bs.all id) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [ih]

theorem all_not (bs : List Bool) : (bs.map Bool.not).all id = !(bs.any id) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [ih]

theorem eval_dual {V : Type} {C : Circ V} (hC : IsMonotoneCirc C) (x : V → Bool) :
    (dual C).eval x = !(C.eval (fun i => !x i)) := by
  induction hC with
  | const b => simp [dual,Circ.depth,Circ.treeSize,Circ.eval]
  | lit v => simp [dual,Circ.eval]
  | and cs hcs ih =>
    have he : cs.map (fun c => (dual c).eval x) =
        (cs.map (fun c => c.eval (fun i => !x i))).map Bool.not := by
      rw [List.map_map]
      apply List.map_congr_left
      intro c hc
      exact ih c hc
    simp only [dual,Circ.eval,List.map_map,Function.comp_def]
    rw [he]
    exact any_not _
  | or cs hcs ih =>
    have he : cs.map (fun c => (dual c).eval x) =
        (cs.map (fun c => c.eval (fun i => !x i))).map Bool.not := by
      rw [List.map_map]
      apply List.map_congr_left
      intro c hc
      exact ih c hc
    simp only [dual,Circ.eval,List.map_map,Function.comp_def]
    rw [he]
    exact all_not _

end SemAC02.P2MMonotoneCircuitDual
end

section
-- Inlined Solutions.P2MCircuitComplement

set_option maxHeartbeats 1000000

namespace SemAC02.P2MCircuitComplement

open SemAC02.P2MMonotoneCircuitDual

theorem flip_flip {V : Type} (C : Circ V) : C.flip.flip = C := by
  cases C with
  | const b => simp [Circ.flip]
  | lit v b => simp [Circ.flip]
  | and cs =>
    simp only [Circ.flip,List.map_map]
    congr 1
    calc
      cs.map (Circ.flip ∘ Circ.flip) = cs.map id := by
        apply List.map_congr_left
        intro c hc
        exact flip_flip c
      _ = cs := List.map_id _
  | or cs =>
    simp only [Circ.flip,List.map_map]
    congr 1
    calc
      cs.map (Circ.flip ∘ Circ.flip) = cs.map id := by
        apply List.map_congr_left
        intro c hc
        exact flip_flip c
      _ = cs := List.map_id _
  | xor cs =>
    simp only [Circ.flip,List.map_map]
    congr 1
    calc
      cs.map (Circ.flip ∘ Circ.flip) = cs.map id := by
        apply List.map_congr_left
        intro c hc
        exact flip_flip c
      _ = cs := List.map_id _
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem flip_injective {V : Type} : Function.Injective (@Circ.flip V) :=
  Function.LeftInverse.injective flip_flip

@[simp] theorem isAnd_flip {V : Type} (C : Circ V) : C.flip.isAnd = C.isAnd := by
  cases C <;> simp [Circ.flip,Circ.isAnd]
@[simp] theorem isOr_flip {V : Type} (C : Circ V) : C.flip.isOr = C.isOr := by
  cases C <;> simp [Circ.flip,Circ.isOr]
@[simp] theorem isXor_flip {V : Type} (C : Circ V) : C.flip.isXor = C.isXor := by
  cases C <;> simp [Circ.flip,Circ.isXor]

theorem reduced_flip {V : Type} {C : Circ V} (hC : IsReduced C) : IsReduced C.flip := by
  induction hC with
  | const b => rw [Circ.flip]; constructor
  | lit v b => rw [Circ.flip]; constructor
  | and cs hn ht hr ih =>
    rw [Circ.flip]
    apply IsReduced.and _ (hn.map flip_injective)
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isAnd_flip] using ht c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
  | or cs hn ht hr ih =>
    rw [Circ.flip]
    apply IsReduced.or _ (hn.map flip_injective)
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isOr_flip] using ht c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
  | xor cs hn ht hr ih =>
    rw [Circ.flip]
    apply IsReduced.xor _ (hn.map flip_injective)
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      simpa only [isXor_flip] using ht c' hc'
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'

theorem depth_flip {V : Type} (C : Circ V) : C.flip.depth = C.depth := by
  cases C with
  | const b => simp [Circ.flip,Circ.depth]
  | lit v b => simp [Circ.flip,Circ.depth]
  | and cs =>
    simp only [Circ.flip,Circ.depth,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => depth_flip c)
  | or cs =>
    simp only [Circ.flip,Circ.depth,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => depth_flip c)
  | xor cs =>
    simp only [Circ.flip,Circ.depth,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => depth_flip c)
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem treeSize_flip {V : Type} (C : Circ V) : C.flip.treeSize = C.treeSize := by
  cases C with
  | const b => simp [Circ.flip,Circ.treeSize]
  | lit v b => simp [Circ.flip,Circ.treeSize]
  | and cs =>
    simp only [Circ.flip,Circ.treeSize,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => treeSize_flip c)
  | or cs =>
    simp only [Circ.flip,Circ.treeSize,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => treeSize_flip c)
  | xor cs =>
    simp only [Circ.flip,Circ.treeSize,List.map_map,Function.comp_def]
    congr 1
    congr 1
    exact List.map_congr_left (fun c hc => treeSize_flip c)
termination_by C
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem noXor_flip {V : Type} {C : Circ V} (hC : NoXor C) : NoXor C.flip := by
  induction hC with
  | const b => rw [Circ.flip]; constructor
  | lit v b => rw [Circ.flip]; constructor
  | and cs hcs ih =>
    rw [Circ.flip]
    apply NoXor.and
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
    exact ih c' hc'
  | or cs hcs ih =>
    rw [Circ.flip]
    apply NoXor.or
    intro c hc
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
    exact ih c' hc'

theorem noXor_of_monotone {V : Type} {C : Circ V} (hC : IsMonotoneCirc C) : NoXor C := by
  induction hC with
  | const b => constructor
  | lit v => constructor
  | and cs hcs ih => exact .and cs ih
  | or cs hcs ih => exact .or cs ih

def negate {V : Type} (C : Circ V) : Circ V := (dual C).flip

theorem eval_negate {V : Type} {C : Circ V} (hC : IsMonotoneCirc C) (x : V → Bool) :
    (negate C).eval x = !C.eval x := by
  simp only [negate,P2MCircuitSemantics.eval_flip,eval_dual hC,Bool.not_not]

theorem depth_negate {V : Type} (C : Circ V) : (negate C).depth = C.depth := by
  rw [negate,depth_flip,depth_dual]

theorem size_negate {V : Type} (C : Circ V) : (negate C).treeSize = C.treeSize := by
  rw [negate,treeSize_flip,size_dual]

theorem reduced_negate {V : Type} {C : Circ V} (hC : IsReduced C) : IsReduced (negate C) :=
  reduced_flip (reduced_dual hC)

theorem noXor_negate {V : Type} {C : Circ V} (hC : IsMonotoneCirc C) : NoXor (negate C) :=
  noXor_flip (noXor_of_monotone (monotone_dual hC))

end SemAC02.P2MCircuitComplement
end

section
-- Inlined Solutions.P2MLiftedCircuitBounds

set_option maxHeartbeats 2000000

namespace SemAC02.P2MLiftedCircuitBounds

open P2MCircuitRenaming P2MCircuitComplement

theorem noXor_rename {V W : Type} (f : V → W) {A : Circ V} (hA : NoXor A) :
    NoXor (A.rename f) := by
  induction hA with
  | const b => rw [Circ.rename]; exact NoXor.const b
  | lit v b => rw [Circ.rename]; exact NoXor.lit _ b
  | and cs h ih =>
    rw [Circ.rename]
    apply NoXor.and
    intro c hc
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    exact ih a ha
  | or cs h ih =>
    rw [Circ.rename]
    apply NoXor.or
    intro c hc
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    exact ih a ha

theorem orChildren_noXor {V : Type} {A : Circ V} (hA : NoXor A) :
    ∀ c ∈ A.orChildren, NoXor c := by
  cases hA with
  | const b => simpa only [Circ.orChildren,List.mem_singleton,forall_eq] using NoXor.const (V:=V) b
  | lit v b => simpa only [Circ.orChildren,List.mem_singleton,forall_eq] using NoXor.lit v b
  | and cs h =>
    intro c hc
    simp only [Circ.orChildren,List.mem_singleton] at hc
    subst c
    exact NoXor.and cs h
  | or cs h => exact h

theorem orChildren_depth {V : Type} {A : Circ V} {d : ℕ}
    (hd : 1 ≤ d) (hA : NoXor A) (hnot : A.isAnd = false) (hdepth : A.depth ≤ d) :
    ∀ c ∈ A.orChildren, c.depth ≤ d-1 := by
  cases hA with
  | const b => simp only [Circ.orChildren,List.mem_singleton,forall_eq,Circ.depth]; omega
  | lit v b => simp only [Circ.orChildren,List.mem_singleton,forall_eq,Circ.depth]; omega
  | and cs h => simp [Circ.isAnd] at hnot
  | or cs h =>
    intro c hc
    rw [Circ.depth] at hdepth
    have hh : c.depth ≤ (cs.map (fun a => a.depth)).foldr max 0 :=
      List.le_max_of_le (List.mem_map.mpr ⟨c,hc,rfl⟩) le_rfl
    omega

theorem orChildren_size {V : Type} (A : Circ V) :
    (A.orChildren.map (fun c => c.treeSize)).sum ≤ A.treeSize := by
  cases A <;> simp [Circ.orChildren,Circ.treeSize]

theorem gadgetH_properties {m d : ℕ} {g : Circ (Fin m)} (hg : IsGadget d g)
    (b : Bool) (j : Fin g.andChildren.length) :
    NoXor (gadgetH g b j) ∧ (gadgetH g b j).isAnd = false ∧
      (gadgetH g b j).depth ≤ d ∧ (gadgetH g b j).treeSize ≤ g.treeSize := by
  rcases hg with ⟨hN,hR,hD,⟨cs,hcs,rfl⟩,hanti,hdisj⟩
  have hj : cs.get j ∈ cs := List.get_mem cs j
  have hN' : NoXor (cs.get j) := by cases hN with | and _ h => exact h _ hj
  have hnot : (cs.get j).isAnd = false := by cases hR with | and _ _ h _ => exact h _ hj
  have hD' : (cs.get j).depth ≤ d := by
    rw [Circ.depth] at hD
    have hh : (cs.get j).depth ≤ (cs.map (fun c => c.depth)).foldr max 0 :=
      List.le_max_of_le (List.mem_map.mpr ⟨_,hj,rfl⟩) le_rfl
    omega
  have hS : (cs.get j).treeSize ≤ (Circ.and cs).treeSize := by
    rw [Circ.treeSize]
    have hh : (cs.get j).treeSize ≤ (cs.map (fun c => c.treeSize)).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨_,hj,rfl⟩)
    omega
  cases b with
  | false => simpa only [gadgetH,Bool.false_eq_true,↓reduceIte,Circ.andChildren] using ⟨hN',hnot,hD',hS⟩
  | true =>
    simp only [gadgetH,↓reduceIte,Circ.andChildren]
    exact ⟨noXor_flip hN',by simpa only [isAnd_flip] using hnot,
      by simpa only [depth_flip] using hD',by simpa only [treeSize_flip] using hS⟩

theorem liftAxiom_noXor {n m d : ℕ} {g : Circ (Fin m)} (hg : IsGadget d g)
    (C : LiftSAParity.Clause (Fin n)) (α : Fin n × Bool → Fin g.andChildren.length) :
    NoXor (liftAxiom g C α) := by
  rw [liftAxiom]
  apply NoXor.or
  intro c hc
  obtain ⟨l,hl,hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
  exact noXor_rename _ (orChildren_noXor (gadgetH_properties hg l.2 (α l)).1 a ha)

theorem liftAxiom_depth {n m d : ℕ} (hd : 1 ≤ d) {g : Circ (Fin m)} (hg : IsGadget d g)
    (C : LiftSAParity.Clause (Fin n)) (α : Fin n × Bool → Fin g.andChildren.length) :
    (liftAxiom g C α).depth ≤ d := by
  rw [liftAxiom,Circ.depth]
  have hm : ((C.toList.flatMap (fun l =>
      ((gadgetH g l.2 (α l)).orChildren).map (Circ.rename (fun j => (l.1,j))))).map
      (fun c => c.depth)).foldr max 0 ≤ d-1 := by
    apply List.max_le_of_forall_le
    intro q hq
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
    obtain ⟨l,hl,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    rw [depth_rename]
    have h := gadgetH_properties hg l.2 (α l)
    exact orChildren_depth hd h.1 h.2.1 h.2.2.1 a ha
  omega

theorem liftAxiom_treeSize {n m d : ℕ} {g : Circ (Fin m)} (hg : IsGadget d g)
    (C : LiftSAParity.Clause (Fin n)) (α : Fin n × Bool → Fin g.andChildren.length) :
    (liftAxiom g C α).treeSize ≤ 1+C.card*g.treeSize := by
  have hb (l : Fin n × Bool) :
      ((((gadgetH g l.2 (α l)).orChildren).map (Circ.rename (fun j => (l.1,j)))).map
        (fun c => c.treeSize)).sum ≤ g.treeSize := by
    simp only [List.map_map,Function.comp_def,size_rename]
    exact (orChildren_size _).trans (gadgetH_properties hg l.2 (α l)).2.2.2
  have hs (ls : List (Fin n × Bool)) :
      ((ls.flatMap (fun l => ((gadgetH g l.2 (α l)).orChildren).map
        (Circ.rename (fun j => (l.1,j))))).map (fun c => c.treeSize)).sum ≤ ls.length*g.treeSize := by
    induction ls with
    | nil => simp
    | cons l ls ih =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,List.length_cons,Nat.add_mul,Nat.one_mul]
      exact (Nat.add_le_add (hb l) ih).trans (by omega)
  have h := hs C.toList
  simpa only [liftAxiom,Circ.treeSize,Finset.length_toList] using Nat.add_le_add_left h 1

theorem lift_properties {n m d : ℕ} (hd : 1 ≤ d) {g : Circ (Fin m)} (hg : IsGadget d g)
    (F : LiftSAParity.CNF (Fin n)) :
    ∀ A ∈ lift g F, A.depth ≤ d ∧ NoXor A := by
  classical
  intro A hA
  obtain ⟨C,hC,hA⟩ := Finset.mem_biUnion.mp hA
  obtain ⟨α,hα,rfl⟩ := Finset.mem_image.mp hA
  exact ⟨liftAxiom_depth hd hg C α,liftAxiom_noXor hg C α⟩

end SemAC02.P2MLiftedCircuitBounds
end

section
-- Inlined Solutions.P2MLiftedFamilySize

set_option maxHeartbeats 2000000

namespace SemAC02.P2MLiftedFamilySize

open Classical

theorem treeSize_pos {V : Type} (A : Circ V) : 1 ≤ A.treeSize := by
  cases A <;> simp [Circ.treeSize]

theorem union_card_le {V : Type} (cs : List (Circ V))
    (h : ∀ c ∈ cs, c.subcircuits.card ≤ c.treeSize) :
    ((cs.map (fun c : Circ V => c.subcircuits)).foldr (· ∪ ·) ∅).card ≤
      (cs.map (fun c => c.treeSize)).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons,List.foldr_cons,List.sum_cons]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (h c (by simp)) (ih (fun a ha => h a (by simp [ha]))))

theorem subcircuits_card_le {V : Type} {A : Circ V} (hA : NoXor A) :
    A.subcircuits.card ≤ A.treeSize := by
  induction hA with
  | const b => simp [Circ.subcircuits,Circ.treeSize]
  | lit v b => simp [Circ.subcircuits,Circ.treeSize]
  | and cs h ih =>
    rw [Circ.subcircuits,Circ.treeSize]
    exact (Finset.card_insert_le _ _).trans (by have hh := union_card_le cs ih; omega)
  | or cs h ih =>
    rw [Circ.subcircuits,Circ.treeSize]
    exact (Finset.card_insert_le _ _).trans (by have hh := union_card_le cs ih; omega)

theorem famSize_le {V : Type} (F : Finset (Circ V)) (T : ℕ)
    (h : ∀ A ∈ F, NoXor A ∧ A.treeSize ≤ T) : famSize F ≤ F.card*T := by
  calc
    _ ≤ ∑ A ∈ F, A.subcircuits.card := Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ F, T := Finset.sum_le_sum (fun A hA => (subcircuits_card_le (h A hA).1).trans (h A hA).2)
    _ = _ := by simp

theorem gadget_arity_pos {m d : ℕ} {g : Circ (Fin m)} (hg : IsGadget d g) :
    1 ≤ g.andChildren.length := by
  obtain ⟨cs,hcs,hroot⟩ := hg.2.2.2.1
  rw [hroot,Circ.andChildren]
  exact List.length_pos_iff.mpr hcs

theorem gadget_arity_le {m d : ℕ} {g : Circ (Fin m)} (hg : IsGadget d g) :
    g.andChildren.length ≤ g.treeSize := by
  obtain ⟨cs,hcs,hroot⟩ := hg.2.2.2.1
  have hl : cs.length ≤ (cs.map (fun c => c.treeSize)).sum := by
    clear hcs hroot
    induction cs with
    | nil => simp
    | cons c cs ih =>
      simp only [List.length_cons,List.map_cons,List.sum_cons]
      have hc := treeSize_pos c
      omega
  rw [hroot,Circ.andChildren,Circ.treeSize]
  omega

theorem liftAxiom_congr {n m : ℕ} (g : Circ (Fin m)) (C : LiftSAParity.Clause (Fin n))
    (α β : Fin n × Bool → Fin g.andChildren.length) (h : ∀ l ∈ C, α l = β l) :
    liftAxiom g C α = liftAxiom g C β := by
  unfold liftAxiom
  congr 1
  apply List.flatMap_congr
  intro l hl
  rw [h l (Finset.mem_toList.mp hl)]

theorem clause_lift_card {n m d : ℕ} {g : Circ (Fin m)} (hg : IsGadget d g)
    (C : LiftSAParity.Clause (Fin n)) :
    (Finset.univ.image (fun α : Fin n × Bool → Fin g.andChildren.length => liftAxiom g C α)).card ≤
      g.andChildren.length^C.card := by
  let j₀ : Fin g.andChildren.length := ⟨0,by have h := gadget_arity_pos hg; omega⟩
  let extend (β : C → Fin g.andChildren.length) : Fin n × Bool → Fin g.andChildren.length :=
    fun l => if hl : l ∈ C then β ⟨l,hl⟩ else j₀
  let S := Finset.univ.image (fun β : C → Fin g.andChildren.length => liftAxiom g C (extend β))
  have hs : Finset.univ.image (fun α : Fin n × Bool → Fin g.andChildren.length => liftAxiom g C α) ⊆ S := by
    intro A hA
    obtain ⟨α,hα,rfl⟩ := Finset.mem_image.mp hA
    refine Finset.mem_image.mpr ⟨(fun l => α l.1),Finset.mem_univ _,?_⟩
    apply liftAxiom_congr
    intro l hl
    simp [extend,hl]
  calc
    _ ≤ S.card := Finset.card_le_card hs
    _ ≤ (Finset.univ : Finset (C → Fin g.andChildren.length)).card := Finset.card_image_le
    _ = _ := by simp

theorem lift_card {n m d w : ℕ} {g : Circ (Fin m)} (hg : IsGadget d g)
    (F : LiftSAParity.CNF (Fin n)) (hw : ∀ C ∈ F, C.card ≤ w) :
    (lift g F).card ≤ F.card*g.treeSize^w := by
  calc
    _ ≤ ∑ C ∈ F, (Finset.univ.image (fun α : Fin n × Bool → Fin g.andChildren.length => liftAxiom g C α)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _C ∈ F, g.treeSize^w := by
      apply Finset.sum_le_sum
      intro C hC
      exact (clause_lift_card hg C).trans
        ((Nat.pow_le_pow_left (gadget_arity_le hg) _).trans
          (Nat.pow_le_pow_right (treeSize_pos g) (hw C hC)))
    _ = _ := by simp

theorem lift_famSize {n m d w : ℕ} {g : Circ (Fin m)} (hg : IsGadget d g)
    (F : LiftSAParity.CNF (Fin n)) (hw : ∀ C ∈ F, C.card ≤ w) :
    famSize (lift g F) ≤ F.card*g.treeSize^w*(1+w*g.treeSize) := by
  have hsize : famSize (lift g F) ≤ (lift g F).card*(1+w*g.treeSize) := by
    apply famSize_le
    intro A hA
    obtain ⟨C,hC,hA⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨α,hα,rfl⟩ := Finset.mem_image.mp hA
    exact ⟨P2MLiftedCircuitBounds.liftAxiom_noXor hg C α,
      (P2MLiftedCircuitBounds.liftAxiom_treeSize hg C α).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hw C hC)) _)⟩
  exact hsize.trans (Nat.mul_le_mul_right _ (lift_card hg F hw))

theorem width_card {n w : ℕ} (hn : 1 ≤ n) (F : LiftSAParity.CNF (Fin n))
    (hw : ∀ C ∈ F, C.card ≤ w) : F.card ≤ (w+1)*(2*n)^w := by
  let B : Finset (LiftSAParity.Clause (Fin n)) :=
    (Finset.range (w+1)).biUnion (fun j => (Finset.univ : Finset (Fin n × Bool)).powersetCard j)
  have hF : F ⊆ B := by
    intro C hC
    refine Finset.mem_biUnion.mpr ⟨C.card,Finset.mem_range.mpr (by have h := hw C hC; omega),?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,rfl⟩
  calc
    _ ≤ B.card := Finset.card_le_card hF
    _ ≤ ∑ j ∈ Finset.range (w+1), ((Finset.univ : Finset (Fin n × Bool)).powersetCard j).card :=
      Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (w+1), (2*n).choose j := by simp [Nat.mul_comm]
    _ ≤ ∑ _j ∈ Finset.range (w+1), (2*n)^w := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right (by omega) (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = _ := by simp

end SemAC02.P2MLiftedFamilySize
end

section
-- Inlined Solutions.P2MSemanticConjunctionRefutation

set_option maxHeartbeats 2000000

namespace SemAC02.P2MSemanticConjunctionRefutation

variable {V : Type}

open Classical

def Rules (F : Set (Circ V)) (π : List (Circ V)) : Prop :=
  ∀ (k : ℕ) (hk : k < π.length),
    π[k] ∈ F ∨ (∀ x : V → Bool, π[k].eval x = true) ∨
    (∃ (i j : ℕ) (hi : i < k) (hj : j < k), ∀ x : V → Bool,
      (π[i]'(hi.trans hk)).eval x = true → (π[j]'(hj.trans hk)).eval x = true →
        π[k].eval x = true)

theorem rules_append {F : Set (Circ V)} {π : List (Circ V)} {A : Circ V}
    (hπ : Rules F π)
    (hA : A ∈ F ∨ (∀ x : V → Bool, A.eval x = true) ∨
      (∃ (i j : ℕ) (hi : i < π.length) (hj : j < π.length), ∀ x : V → Bool,
        π[i].eval x = true → π[j].eval x = true → A.eval x = true)) :
    Rules F (π ++ [A]) := by
  intro k hk
  by_cases h : k < π.length
  · rw [List.getElem_append_left h]
    rcases hπ k h with ha | ht | ⟨i,j,hi,hj,hij⟩
    · exact Or.inl ha
    · exact Or.inr (Or.inl ht)
    · refine Or.inr (Or.inr ⟨i,j,hi,hj,?_⟩)
      simpa only [List.getElem_append_left (hi.trans h),List.getElem_append_left (hj.trans h)] using hij
  · have he : k = π.length := by simp only [List.length_append,List.length_singleton] at hk; omega
    subst k
    rw [List.getElem_append_right (le_refl π.length)]
    simp only [Nat.sub_self,List.getElem_cons_zero]
    rcases hA with ha | ht | ⟨i,j,hi,hj,hij⟩
    · exact Or.inl ha
    · exact Or.inr (Or.inl ht)
    · refine Or.inr (Or.inr ⟨i,j,hi,hj,?_⟩)
      simpa only [List.getElem_append_left hi,List.getElem_append_left hj] using hij

def conjunctionProof : List (Circ V) → List (Circ V)
  | [] => [Circ.and []]
  | c :: cs => conjunctionProof cs ++ [c, Circ.and (c :: cs)]

theorem proof_last (cs : List (Circ V)) :
    (conjunctionProof cs).getLast? = some (Circ.and cs) := by
  cases cs <;> simp [conjunctionProof]

theorem proof_nonempty (cs : List (Circ V)) : 0 < (conjunctionProof cs).length := by
  cases cs <;> simp [conjunctionProof]

theorem proof_rules (F : Set (Circ V)) (cs : List (Circ V)) (hF : ∀ c ∈ cs, c ∈ F) :
    Rules F (conjunctionProof cs) := by
  induction cs with
  | nil =>
    intro k hk
    change k < 1 at hk
    have hk0 : k = 0 := by omega
    subst k
    exact Or.inr (Or.inl (by intro x; simp [conjunctionProof,Circ.eval]))
  | cons c cs ih =>
    have hp := ih (fun a ha => hF a (List.mem_cons_of_mem c ha))
    have hc : Rules F (conjunctionProof cs ++ [c]) := rules_append hp (Or.inl (hF c (by simp)))
    have hlen := proof_nonempty cs
    have hlast : (conjunctionProof cs)[(conjunctionProof cs).length-1] = Circ.and cs := by
      have h := proof_last cs
      rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by omega)] at h
      exact Option.some.inj h
    have hr : Rules F ((conjunctionProof cs ++ [c]) ++ [Circ.and (c::cs)]) :=
      rules_append hc (Or.inr (Or.inr ⟨(conjunctionProof cs).length-1,
      (conjunctionProof cs).length,by simp,by simp,by
        intro x hs hc
        rw [List.getElem_append_left (by omega),hlast] at hs
        rw [List.getElem_append_right (le_refl _)] at hc
        simp only [Nat.sub_self,List.getElem_cons_zero] at hc
        simpa only [Circ.eval,List.map_cons,List.all_cons,Bool.and_eq_true,id_eq] using And.intro hc hs⟩))
    simpa only [conjunctionProof,List.append_assoc,List.singleton_append] using hr

theorem depth_and_le (cs : List (Circ V)) (d : ℕ) (h : ∀ c ∈ cs, c.depth ≤ d) :
    (Circ.and cs).depth ≤ d+1 := by
  have hm : (cs.map (fun c => c.depth)).foldr max 0 ≤ d := by
    induction cs with
    | nil => simp
    | cons c cs ih =>
      simp only [List.map_cons,List.foldr_cons,max_le_iff]
      exact ⟨h c (by simp),ih (fun a ha => h a (by simp [ha]))⟩
  rw [Circ.depth]
  omega

theorem proof_depth (cs : List (Circ V)) (d : ℕ) (h : ∀ c ∈ cs, c.depth ≤ d) :
    ∀ A ∈ conjunctionProof cs, A.depth ≤ d+1 := by
  induction cs with
  | nil => intro A hA; simp only [conjunctionProof,List.mem_singleton] at hA; subst A; simp [Circ.depth]
  | cons c cs ih =>
    intro A hA
    simp only [conjunctionProof,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hA
    rcases hA with hA | rfl | rfl
    · exact ih (fun a ha => h a (by simp [ha])) A hA
    · exact (h A (by simp)).trans (Nat.le_succ d)
    · exact depth_and_le _ _ h

theorem proof_noXor (cs : List (Circ V)) (h : ∀ c ∈ cs, NoXor c) :
    ∀ A ∈ conjunctionProof cs, NoXor A := by
  induction cs with
  | nil => intro A hA; simp only [conjunctionProof,List.mem_singleton] at hA; subst A; exact NoXor.and [] (by simp)
  | cons c cs ih =>
    intro A hA
    simp only [conjunctionProof,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hA
    rcases hA with hA | rfl | rfl
    · exact ih (fun a ha => h a (by simp [ha])) A hA
    · exact h A (by simp)
    · exact NoXor.and _ h

open Classical in
noncomputable def nodes (cs : List (Circ V)) : Finset (Circ V) :=
  cs.toFinset.biUnion Circ.subcircuits

open Classical in
noncomputable def roots : List (Circ V) → Finset (Circ V)
  | [] => {Circ.and []}
  | c :: cs => insert (Circ.and (c::cs)) (roots cs)

theorem roots_card (cs : List (Circ V)) : (roots cs).card ≤ cs.length+1 := by
  classical
  induction cs with
  | nil => simp [roots]
  | cons c cs ih =>
    exact (Finset.card_insert_le _ _).trans (by simpa only [List.length_cons] using Nat.add_le_add_right ih 1)

theorem and_nodes (cs : List (Circ V)) :
    (Circ.and cs).subcircuits = insert (Circ.and cs) (nodes cs) := by
  classical
  have h : (cs.map (fun c => c.subcircuits)).foldr (· ∪ ·) ∅ = nodes cs := by
    induction cs with
    | nil => simp [nodes]
    | cons c cs ih => simp [nodes,List.toFinset_cons,ih,nodes]
  rw [Circ.subcircuits,h]

theorem nodes_cons (c : Circ V) (cs : List (Circ V)) :
    nodes (c::cs) = c.subcircuits ∪ nodes cs := by
  classical
  simp [nodes]

theorem proof_nodes (cs : List (Circ V)) :
    nodes (conjunctionProof cs) ⊆ nodes cs ∪ roots cs := by
  classical
  induction cs with
  | nil => simp [conjunctionProof,nodes,Circ.subcircuits,roots]
  | cons c cs ih =>
    intro A hA
    have hn : nodes (conjunctionProof (c::cs)) = nodes (conjunctionProof cs) ∪
        (c.subcircuits ∪ (Circ.and (c::cs)).subcircuits) := by
      simp [conjunctionProof,nodes,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]
    rw [hn] at hA
    have ha := ih
    rw [nodes_cons,roots]
    rw [and_nodes,nodes_cons] at hA
    simp only [Finset.mem_union,Finset.mem_insert] at hA ⊢
    have hai : ∀ A ∈ nodes (conjunctionProof cs), A ∈ nodes cs ∨ A ∈ roots cs := by
      intro A hA
      exact Finset.mem_union.mp (ha hA)
    rcases hA with hp | hc | he | hc | hcs
    · rcases hai A hp with hcs | hr
      · exact Or.inl (Or.inr hcs)
      · exact Or.inr (Or.inr hr)
    · exact Or.inl (Or.inl hc)
    · exact Or.inr (Or.inl he)
    · exact Or.inl (Or.inl hc)
    · exact Or.inl (Or.inr hcs)

theorem refutation {d : ℕ} (F : Finset (Circ V))
    (hdepth : ∀ A ∈ F, A.depth ≤ d) (hxor : ∀ A ∈ F, NoXor A)
    (hunsat : ¬∃ x : V → Bool, ∀ A ∈ F, A.eval x = true) :
    ∃ π : List (Circ V), IsSemRefutation (d+1) (F : Set (Circ V)) π ∧
      (∀ A ∈ π, NoXor A) ∧ proofSize π ≤ famSize F + F.card + 2 := by
  classical
  let cs := F.toList
  let p := conjunctionProof cs
  let π := p ++ [Circ.const false]
  have hpr : Rules (F : Set (Circ V)) p := proof_rules _ cs (by simp [cs])
  have hlen : 0 < p.length := proof_nonempty cs
  have hlast : p[p.length-1] = Circ.and cs := by
    have h := proof_last cs
    rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by change p.length-1 < p.length; omega)] at h
    exact Option.some.inj h
  have hπr : Rules (F : Set (Circ V)) π := rules_append hpr (Or.inr (Or.inr
    ⟨p.length-1,p.length-1,by omega,by omega,by
      intro x hp _
      rw [hlast] at hp
      apply False.elim
      apply hunsat
      refine ⟨x,?_⟩
      intro A hA
      have ha : A ∈ cs := by simpa [cs] using hA
      have hall : ∀ a ∈ cs, a.eval x = true := by
        simpa only [Circ.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,id_eq] using hp
      exact hall A ha⟩))
  refine ⟨π,⟨?_,hπr,by simp [π]⟩,?_,?_⟩
  · intro A hA
    rcases List.mem_append.mp hA with hA | hA
    · exact proof_depth cs d (by simpa [cs] using hdepth) A hA
    · simp only [List.mem_singleton] at hA
      subst A
      simp [Circ.depth]
  · intro A hA
    rcases List.mem_append.mp hA with hA | hA
    · exact proof_noXor cs (by simpa [cs] using hxor) A hA
    · simp only [List.mem_singleton] at hA
      subst A
      exact NoXor.const false
  · have hnodes : nodes π ⊆ insert (Circ.const false) (nodes cs ∪ roots cs) := by
      intro A hA
      have he : nodes π = nodes p ∪ {Circ.const false} := by
        simp [π,nodes,Circ.subcircuits]
      rw [he] at hA
      rcases Finset.mem_union.mp hA with hA | hA
      · exact Finset.mem_insert_of_mem (proof_nodes cs hA)
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hA))
    have hc := (Finset.card_le_card hnodes).trans (Finset.card_insert_le _ _)
    have hu := Finset.card_union_le (nodes cs) (roots cs)
    have hr := roots_card cs
    have he : (nodes cs).card = famSize F := by simp [nodes,cs,famSize]
    have hl : cs.length = F.card := by simp [cs]
    change (nodes π).card ≤ _
    omega

end SemAC02.P2MSemanticConjunctionRefutation
end

section
-- Inlined Solutions.P2MLiftedUpperRefutation

namespace SemAC02.P2MLiftedUpperRefutation

theorem self_mem_subcircuits {V : Type} (A : Circ V) : A ∈ A.subcircuits := by
  classical
  cases A <;> simp only [Circ.subcircuits,Finset.mem_insert,Finset.mem_singleton,true_or]

theorem card_le_famSize {V : Type} (F : Finset (Circ V)) : F.card ≤ famSize F := by
  classical
  apply Finset.card_le_card
  intro A hA
  exact Finset.mem_biUnion.mpr ⟨A,hA,self_mem_subcircuits A⟩

theorem upper_refutation {n m d : ℕ} (hd : 2 ≤ d) {g : Circ (Fin m)} (hg : IsGadget d g)
    (F : LiftSAParity.CNF (Fin n)) (hF : ¬LiftSAParity.Satisfiable F) :
    ∃ π : List (Circ (Fin n × Fin m)),
      IsSemRefutation (d+1) (lift g F : Set (Circ (Fin n × Fin m))) π ∧
        (∀ A ∈ π, NoXor A) ∧ proofSize π ≤ 2*famSize (lift g F)+2 := by
  have h := P2MLiftedCircuitBounds.lift_properties (by omega : 1 ≤ d) hg F
  obtain ⟨π,hπ,hxor,hsize⟩ := P2MSemanticConjunctionRefutation.refutation (lift g F)
    (fun A hA => (h A hA).1) (fun A hA => (h A hA).2)
    (proposition_8_3_lift_unsat hd g hg F hF)
  exact ⟨π,hπ,hxor,by have hc := card_le_famSize (lift g F); omega⟩

end SemAC02.P2MLiftedUpperRefutation
end

section
-- Inlined Solutions.P2MLiftedPolynomialUpperBound

namespace SemAC02.P2MLiftedPolynomialUpperBound

theorem base_card {n w : ℕ} (hn : 2 ≤ n) (hw : w+1 ≤ n)
    (F : LiftSAParity.CNF (Fin n)) (hF : ∀ C ∈ F, C.card ≤ w) :
    F.card ≤ n^(2*w+1) := by
  have h2 : 2*n ≤ n^2 := by nlinarith
  calc
    _ ≤ (w+1)*(2*n)^w := P2MLiftedFamilySize.width_card (by omega) F hF
    _ ≤ n*(n^2)^w := Nat.mul_le_mul hw (Nat.pow_le_pow_left h2 _)
    _ = _ := by rw [← pow_mul,pow_succ]; ac_rfl

theorem family_bound {n m d w a : ℕ} (hn : 2 ≤ n) (hw : w+1 ≤ n)
    {g : Circ (Fin m)} (hg : IsGadget d g) (hsize : g.treeSize ≤ n^a)
    (F : LiftSAParity.CNF (Fin n)) (hF : ∀ C ∈ F, C.card ≤ w) :
    famSize (lift g F) ≤ n^((a+2)*(w+1)) := by
  have hc := base_card hn hw F hF
  have hgpow : g.treeSize^w ≤ n^(a*w) := by
    simpa only [pow_mul] using Nat.pow_le_pow_left hsize w
  have ht : 1+w*g.treeSize ≤ n^(a+1) := by
    calc
      _ ≤ g.treeSize+w*g.treeSize := Nat.add_le_add_right (P2MLiftedFamilySize.treeSize_pos g) _
      _ = (w+1)*g.treeSize := by ring
      _ ≤ n*n^a := Nat.mul_le_mul hw hsize
      _ = n^(a+1) := by rw [pow_succ]; ac_rfl
  calc
    _ ≤ F.card*g.treeSize^w*(1+w*g.treeSize) := P2MLiftedFamilySize.lift_famSize hg F hF
    _ ≤ n^(2*w+1)*n^(a*w)*n^(a+1) := Nat.mul_le_mul (Nat.mul_le_mul hc hgpow) ht
    _ = _ := by rw [← pow_add,← pow_add]; congr 1; ring

/-- The polynomial upper-size part of Theorem 8.1, with an explicit exponent independent of
the PC-degree growth exponent. -/
theorem polynomial_upper {n m d w a : ℕ} (hd : 2 ≤ d) (hn : 2 ≤ n) (hw : w+1 ≤ n)
    {g : Circ (Fin m)} (hg : IsGadget d g) (hsize : g.treeSize ≤ n^a)
    (F : LiftSAParity.CNF (Fin n)) (hF : ¬LiftSAParity.Satisfiable F)
    (hwidth : ∀ C ∈ F, C.card ≤ w) :
    famSize (lift g F) ≤ n^((a+2)*(w+1)+2) ∧
      ∃ π : List (Circ (Fin n × Fin m)),
        IsSemRefutation (d+1) (lift g F : Set (Circ (Fin n × Fin m))) π ∧
          (∀ A ∈ π, NoXor A) ∧ proofSize π ≤ n^((a+2)*(w+1)+2) := by
  let K := (a+2)*(w+1)
  have hfamily : famSize (lift g F) ≤ n^K := family_bound hn hw hg hsize F hwidth
  have hpow : 1 ≤ n^K := one_le_pow₀ (by omega)
  have hbig : 2*famSize (lift g F)+2 ≤ n^(K+2) := by
    calc
      _ ≤ 4*n^K := by omega
      _ ≤ n^2*n^K := Nat.mul_le_mul_right _ (by nlinarith : 4 ≤ n^2)
      _ = _ := by rw [← pow_add]; congr 1; omega
  obtain ⟨π,hπ,hxor,hπsize⟩ := P2MLiftedUpperRefutation.upper_refutation hd hg F hF
  exact ⟨hfamily.trans (Nat.pow_le_pow_right (by omega) (by omega)),
    π,hπ,hxor,hπsize.trans hbig⟩

end SemAC02.P2MLiftedPolynomialUpperBound
end

section
-- Inlined Solutions.P2MRelativePC

open MvPolynomial AC02Frege SemAC02
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q ∈ U) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) : Derivable P U 0 := Or.inl rfl

theorem pc_mem {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))}
    {U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) : p ∈ U := by
  rcases hp with rfl | ⟨π,_,hmem,hp⟩
  · exact U.zero_mem
  · exact hmem p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (c : ZMod 2) :
    Derivable P U (c • p) := by
  rcases hp with rfl | ⟨π,hπ,hmem,hp⟩
  · simp only [smul_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; left
    exact ⟨i,i,hi,hi,c,0,by simp only [hpi,zero_smul,add_zero]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hmem q hq
    · have he : q = c • p := List.mem_singleton.mp hq
      rw [he]
      exact U.smul_mem c (hmem p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p q : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (hq : Derivable P U q) :
    Derivable P U (p+q) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ,hρ,hρmem,hq⟩
  · simpa only [add_zero] using (show Derivable P U p from Or.inr ⟨π,hπ,hπmem,hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j,hj,hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p+q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i,j,hi,hj,1,1,by simp only [hpi,hqj,one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπmem r hr
      · exact hρmem r hr
    · have he : r = p+q := List.mem_singleton.mp hr
      rw [he]
      exact U.add_mem (hπmem p hp) (hρmem q hq)

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (v : Fin n)
    (hmem : ML (X v * p) ∈ U) : Derivable P U (ML (X v * p)) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simp only [mul_zero,map_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i,hi,v,by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπmem q hq
    · rwa [List.mem_singleton.mp hq]

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P) (hmem : ML p ∈ U) :
    Derivable P U (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hmem, by simp⟩
  intro k hk
  have he : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p,hp,1,by simp⟩

end SemAC02.P2MRelativePC
end

section
-- Inlined Solutions.RelativePCPolynomialMultiplication

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePC

theorem pc_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (u v : MvPolynomial (Fin n) (ZMod 2)) (hu : Derivable P U u) (huml : IsMultilinear u)
    (hmem : ∀ w : MvPolynomial (Fin n) (ZMod 2), w.totalDegree ≤ v.totalDegree → ML (u*w) ∈ U) :
    Derivable P U (ML (u*v)) := by
  classical
  induction v using MvPolynomial.induction_on'' with
  | C c =>
    have he : u * C c = c • u := by rw [smul_eq_C_mul, mul_comm]
    rw [he, map_smul, ml_of_multilinear u huml]
    exact pc_smul P U hu c
  | monomial_add s c p hnot hc ihp ihm =>
    have hdis : Disjoint (monomial s c).support p.support := by
      apply disjoint_support_monomial
      · exact hnot
      · exact hc
    have hsupp : (monomial s c + p).support = (monomial s c).support ∪ p.support := by
      exact Finsupp.support_add_eq hdis
    have hdm : (monomial s c).totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_left
    have hdp : p.totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_right
    rw [mul_add, map_add]
    exact pc_add P U (ihm (fun w hw => hmem w (hw.trans hdm)))
      (ihp (fun w hw => hmem w (hw.trans hdp)))
  | mul_X p i ih =>
    have hle : p.totalDegree ≤ (p * X i).totalDegree := by
      by_cases hp : p = 0
      · simp [hp]
      · rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
        omega
    have hi := ih (fun w hw => hmem w (hw.trans hle))
    have he : ML (u * (p * X i)) = ML (X i * ML (u*p)) := by
      rw [ml_mul_right]
      congr 1
      ring
    rw [he]
    apply pc_mul_X P U hi i
    rw [← he]
    exact hmem _ le_rfl

end SemAC02.P2MRelativePC
end

section
-- Inlined Solutions.P2MClauseEvaluation

open MvPolynomial AC02Frege LiftSAParity

namespace SemAC02.P2MClauseEvaluation

attribute [local instance] Classical.propDecidable

theorem litPoly_eval {V : Type} (l : V × Bool) (z : V → Bool) :
    eval (toF2 z) (litPoly l) = if z l.1 = l.2 then 1 else 0 := by
  rcases l with ⟨i,b⟩
  cases b <;> cases h : z i <;> simp [litPoly,toF2,h,CharTwo.add_self_eq_zero]

theorem clauseCompl_eval {V : Type} (C : Clause V) (z : V → Bool) :
    eval (toF2 z) (clauseCompl C) = if Falsifies z C then 1 else 0 := by
  classical
  simp only [clauseCompl,map_prod,map_add,map_one,litPoly_eval]
  by_cases h : Falsifies z C
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro l hl
    rw [if_neg (h l hl),add_zero]
  · rw [if_neg h]
    obtain ⟨l,hl,he⟩ : ∃ l ∈ C, z l.1 = l.2 := by by_contra! hn; exact h hn
    exact Finset.prod_eq_zero hl (by rw [if_pos he,CharTwo.add_self_eq_zero])

end SemAC02.P2MClauseEvaluation
end

section
-- Inlined Solutions.P2MBooleanLocality

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MBooleanLocality

theorem multilinear_degree_le_card {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) : p.totalDegree ≤ Fintype.card V := by
  classical
  apply Finset.sup_le
  intro s hs
  rw [squarefree_sum s (hp s hs)]
  exact Finset.card_le_univ _

noncomputable def extendAssignment {V : Type} (J : Finset V) (x : J → ZMod 2) : V → Bool := by
  classical
  exact fun i => if hi : i ∈ J then decide (x ⟨i, hi⟩ = 1) else false

theorem represents_local_function {V : Type} [Fintype V] (J : Finset V)
    (f : (V → Bool) → ZMod 2)
    (hf : ∀ z z' : V → Bool, (∀ i ∈ J, z i = z' i) → f z = f z') :
    ∃ r : MvPolynomial V (ZMod 2), r.totalDegree ≤ J.card ∧
      ∀ z : V → Bool, eval (toF2 z) r = f z := by
  classical
  let η : (J → ZMod 2) → ZMod 2 := fun x => f (extendAssignment J x)
  obtain ⟨p, hp⟩ := LinearMap.range_eq_top.mp (MvPolynomial.range_evalᵢ J (ZMod 2)) η
  let p' : restrictDegree J (ZMod 2) (Fintype.card (ZMod 2) - 1) := p
  have hml : IsMultilinear p'.1 := by
    apply (mem_restrictDegree J _ 1).mp
    simpa only [ZMod.card, Nat.reduceSub] using p'.2
  refine ⟨rename Subtype.val p'.1, ?_, ?_⟩
  · apply (totalDegree_rename_le _ _).trans
    simpa only [Fintype.card_coe] using multilinear_degree_le_card p'.1 hml
  · intro z
    rw [eval_rename]
    have he := congrFun hp (fun j : J => toF2 z j.1)
    change eval (fun j : J => toF2 z j.1) p'.1 = f (extendAssignment J (fun j : J => toF2 z j.1)) at he
    change eval (fun j : J => toF2 z j.1) p'.1 = f z
    rw [he]
    apply hf
    intro i hi
    simp only [extendAssignment, dif_pos hi]
    cases h : z i <;> simp [toF2, h]

end SemAC02.P2MBooleanLocality
end

section
-- Inlined Solutions.P2MBooleanPCCompleteness

set_option maxHeartbeats 2000000

open MvPolynomial AC02Frege LiftSAParity
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis AC02Frege.P2MMajorityFoundation

namespace SemAC02.P2MBooleanPCCompleteness

theorem relative_sum {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) (ZMod 2))
    (hf : ∀ i ∈ I, P2MRelativePC.Derivable P U (f i)) : P2MRelativePC.Derivable P U (∑ i ∈ I, f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using P2MRelativePC.pc_zero P U
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact P2MRelativePC.pc_add P U (hf i (Finset.mem_insert_self i I))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Completeness for the reduced Boolean PC model: an unsatisfiable CNF has a refutation
whose lines all have degree at most the number of variables. -/
theorem exists_refutation {n : ℕ} (F : CNF (Fin n)) (hF : ¬Satisfiable F) :
    ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
      PCNonBool.IsRefutation ML (SemAC02.pcAxioms F) π ∧ ∀ p ∈ π, p.totalDegree ≤ n := by
  classical
  let P := SemAC02.pcAxioms F
  let U := restrictDegree (Fin n) (ZMod 2) 1
  have hmem (p : MvPolynomial (Fin n) (ZMod 2)) : ML p ∈ U :=
    (mem_restrictDegree _ _ 1).mpr (ml_multilinear p)
  have hpoint (S : Finset (Fin n)) : P2MRelativePC.Derivable P U (pointPoly S) := by
    let X : Fin n → Bool := fun i => decide (i ∈ S)
    obtain ⟨C,hCF,hfalse⟩ : ∃ C ∈ F, Falsifies X C := by
      by_contra! hn
      exact hF ⟨X,hn⟩
    have hf := P2MClauseEvaluation.clauseCompl_eval C X
    rw [if_pos hfalse] at hf
    have hX : SemAC02.toF2 X = (fun i => if i ∈ S then (1 : ZMod 2) else 0) := by
      funext i
      simp [SemAC02.toF2,X]
    have hf' : eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) (clauseCompl C) = 1 := by
      rw [hX] at hf
      exact hf
    have hax := P2MRelativePC.pc_axiom P U (clauseCompl C) (show clauseCompl C ∈ P from ⟨C,hCF,rfl⟩)
      (hmem _)
    have hprod := P2MRelativePC.pc_polynomial_mul P U (ML (clauseCompl C)) (pointPoly S) hax
      (ml_multilinear _) (fun _ _ => hmem _)
    have heq : ML (ML (clauseCompl C)*pointPoly S) = pointPoly S := by
      apply multilinear_ext (ml_multilinear _) (pointPoly_multilinear S)
      intro x
      simp only [eval_ml,map_mul,pointPoly_eval]
      by_cases hx : x = (fun i => if i ∈ S then (1 : ZMod 2) else 0)
      · simp only [if_pos hx,mul_one]
        rw [hx,hf']
      · simp only [if_neg hx,mul_zero]
    rwa [heq] at hprod
  have hOne : IsMultilinear (1 : MvPolynomial (Fin n) (ZMod 2)) := by
    simpa only [xMon,Finset.prod_empty] using xMon_multilinear (∅ : Finset (Fin n))
  have hsum : (∑ S : Finset (Fin n), pointPoly S) = (1 : MvPolynomial (Fin n) (ZMod 2)) := by
    have h := point_interpolation (1 : MvPolynomial (Fin n) (ZMod 2)) hOne
    simpa only [map_one,one_smul] using h.symm
  have hd : P2MRelativePC.Derivable P U (1 : MvPolynomial (Fin n) (ZMod 2)) := by
    rw [← hsum]
    exact relative_sum P U Finset.univ pointPoly (fun S _ => hpoint S)
  rcases hd with hz | ⟨π,hπ,hspace,h1⟩
  · exact False.elim (one_ne_zero hz)
  · refine ⟨π,⟨hπ,h1⟩,?_⟩
    intro p hp
    have hml : IsMultilinear p := (mem_restrictDegree _ _ 1).mp (hspace p hp)
    simpa only [Fintype.card_fin] using P2MBooleanLocality.multilinear_degree_le_card p hml

theorem degree_upper {n Δ : ℕ} (F : CNF (Fin n)) (hF : ¬Satisfiable F) (hΔ : PCDegreeAtLeast F Δ) :
    Δ ≤ n := by
  obtain ⟨π,hπ,hdeg⟩ := exists_refutation F hF
  obtain ⟨p,hp,hpΔ⟩ := hΔ π hπ
  exact hpΔ.trans (hdeg p hp)

end SemAC02.P2MBooleanPCCompleteness
end

section
-- Inlined Solutions.P2MLiftedLowerBound

set_option maxHeartbeats 2000000

open Filter

namespace SemAC02.P2MLiftedLowerBound

theorem lifted_lower_bound :
    ∀ d : ℕ, 2 ≤ d → ∃ c : ℝ, 0 < c ∧ ∀ w₀ : ℕ, ∃ K : ℕ, ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ F : LiftSAParity.CNF (Fin n), ¬ LiftSAParity.Satisfiable F →
        (∀ Cl ∈ F, Cl.card ≤ w₀) → ∀ Δ : ℕ, (n : ℝ) ^ C ≤ (Δ : ℝ) → PCDegreeAtLeast F Δ →
          ∃ (m : ℕ) (g : Circ (Fin m)), IsGadget d g ∧
            famSize (lift g F) ≤ n ^ K ∧
            (∀ π : List (Circ (Fin n × Fin m)),
              IsSemRefutation d (lift g F : Set (Circ (Fin n × Fin m))) π →
                Real.exp (c * Real.log n * (Real.log Δ) ^ ((1 : ℝ) / ((d : ℝ) - 1))) ≤
                  (proofSize π : ℝ)) ∧
            (∃ π : List (Circ (Fin n × Fin m)),
              IsSemRefutation (d + 1) (lift g F : Set (Circ (Fin n × Fin m))) π ∧
                (∀ A ∈ π, NoXor A) ∧ proofSize π ≤ n ^ K) := by
  intro d hd
  let c := Real.exp (-1)/128
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  intro w
  obtain ⟨a,hgadgets⟩ := P2MLiftedGadgetSelection.polynomial_gadgets d hd
  refine ⟨(a+2)*(w+1)+2,?_⟩
  intro C hC
  have hall : ∀ᶠ n : ℕ in atTop, ∀ F : LiftSAParity.CNF (Fin n), ¬LiftSAParity.Satisfiable F →
      (∀ Cl ∈ F, Cl.card ≤ w) → ∀ Δ : ℕ, (n : ℝ)^C ≤ (Δ : ℝ) → PCDegreeAtLeast F Δ →
        ∃ (m : ℕ) (g : Circ (Fin m)), IsGadget d g ∧
          famSize (lift g F) ≤ n^((a+2)*(w+1)+2) ∧
          (∀ π : List (Circ (Fin n × Fin m)), IsSemRefutation d (lift g F : Set (Circ (Fin n × Fin m))) π →
            Real.exp (c*Real.log n*(Real.log Δ)^((1 : ℝ)/((d : ℝ)-1))) ≤ (proofSize π : ℝ)) ∧
          (∃ π : List (Circ (Fin n × Fin m)), IsSemRefutation (d+1) (lift g F : Set (Circ (Fin n × Fin m))) π ∧
            (∀ A ∈ π, NoXor A) ∧ proofSize π ≤ n^((a+2)*(w+1)+2)) := by
    filter_upwards [hgadgets,P2MLiftedAsymptoticParameters.eventual_parameters d hd C hC,
      P2MLiftedParameterFoundations.eventually_log_power_le (130*(32 : ℝ)^(2*d-1)) (2*d-1) (by norm_num : (0 : ℝ) < 1),
      eventually_ge_atTop 2,eventually_ge_atTop (w+1),P2MLiftedParameterFoundations.eventually_log_large 1]
      with n hgadget hparameters hM hn hw hlog
    intro F hF hwidth Δ hlow hPC
    let L := 32*Real.log (n : ℝ)
    let ε := (L^(d-1))⁻¹
    obtain ⟨m,g,hε,hεmax,hg,hsize,hml,hmhi,hdim⟩ := hgadget
    have hL : 1 ≤ L := by dsimp [L]; linarith
    have hscale : ε^(-1/((d : ℝ)-1)) = L :=
      P2MLiftedParameterFoundations.scale_inverse_power hd (by linarith)
    have hmN : m ≤ n := by
      have hpow : 130*L^(2*d-1) ≤ (n : ℝ) := by
        calc
          _ = (130*(32 : ℝ)^(2*d-1))*(Real.log (n : ℝ))^(2*d-1) := by dsimp [L]; rw [mul_pow]; ring
          _ ≤ _ := by simpa only [Real.rpow_one] using hM
      exact_mod_cast hmhi.trans hpow
    have hΔn : Δ ≤ n := P2MBooleanPCCompleteness.degree_upper F hF hPC
    obtain ⟨r,R,hr,hR,hgap,hrT,hbottom,htop,hbudget,hlarge⟩ := hparameters Δ hlow hΔn
    have hbudgets := P2MLiftedDimensionBudgets.dimension_budgets hd (by omega : 1 ≤ n) hε hL hscale hml hbudget
    have hα : (1/2 : ℝ) ≤
        (Module.finrank (ZMod 2) (multiplierSpace (fun X => g.eval X) n
          ⌊(1/2-ε)*((n*m : ℕ) : ℝ)⌋₊) : ℝ)/(Hn (n*m) ⌊(1/2-ε)*((n*m : ℕ) : ℝ)⌋₊ : ℝ) := by
      have hcut : 0 ≤ (1/2-ε)*((n*m : ℕ) : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
      have hdensity := hdim ⌊(1/2-ε)*((n*m : ℕ) : ℝ)⌋₊ (Nat.floor_le hcut)
      have herror := P2MLiftedDimensionBudgets.density_error hn hmN
      change (((n*m : ℕ) : ℝ)+1)*n*Real.exp (-L) ≤ 1/2 at herror
      linarith
    obtain ⟨hfam,hupper⟩ := P2MLiftedPolynomialUpperBound.polynomial_upper hd hn hw hg hsize F hF hwidth
    refine ⟨m,g,hg,hfam,?_,hupper⟩
    intro π hπ
    have hnumeric := P2MLiftedNumericLowerBound.lower_bound hd hg F hF hPC hr hR hgap ε hε hεmax
      hbudgets.1 hbudgets.2 (1/2) hα π hπ
    have hbottom' : 128*ε*(r : ℝ)^((d-1)-1) ≤ 1 := by
      simpa only [show d-1-1 = d-2 by omega] using hbottom
    have hfinal := P2MLiftedFinalExponent.final_exponent (p:=d-1) hrT hbottom' htop hlarge
    simp only [show d-1-1 = d-2 by omega] at hfinal
    have hpcast : ((d-1 : ℕ) : ℝ) = (d : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ d),Nat.cast_one]
    simpa only [hpcast,mul_assoc] using hfinal.trans hnumeric
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hall
  exact ⟨n₀,hn₀⟩

end SemAC02.P2MLiftedLowerBound
end

end P2MRootProof
open SemAC02

theorem solution :
    ∀ d : ℕ, 2 ≤ d → ∃ c : ℝ, 0 < c ∧ ∀ w₀ : ℕ, ∃ K : ℕ, ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ F : LiftSAParity.CNF (Fin n), ¬ LiftSAParity.Satisfiable F →
        (∀ Cl ∈ F, Cl.card ≤ w₀) → ∀ Δ : ℕ, (n : ℝ) ^ C ≤ (Δ : ℝ) → PCDegreeAtLeast F Δ →
          ∃ (m : ℕ) (g : Circ (Fin m)), IsGadget d g ∧
            famSize (lift g F) ≤ n ^ K ∧
            (∀ π : List (Circ (Fin n × Fin m)),
              IsSemRefutation d (lift g F : Set (Circ (Fin n × Fin m))) π →
                Real.exp (c * Real.log n * (Real.log Δ) ^ ((1 : ℝ) / ((d : ℝ) - 1))) ≤
                  (proofSize π : ℝ)) ∧
            (∃ π : List (Circ (Fin n × Fin m)),
              IsSemRefutation (d + 1) (lift g F : Set (Circ (Fin n × Fin m))) π ∧
                (∀ A ∈ π, NoXor A) ∧ proofSize π ≤ n ^ K)  := by
  exact P2MRootProof.SemAC02.P2MLiftedLowerBound.lifted_lower_bound
