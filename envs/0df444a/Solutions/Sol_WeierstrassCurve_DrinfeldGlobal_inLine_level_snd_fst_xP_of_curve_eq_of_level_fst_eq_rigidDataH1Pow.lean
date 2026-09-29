-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.inLine_level_snd_fst_xP_of_curve_eq_of_level_fst_eq_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/33802d27-a3dd-5b97-a007-99d2016e8621

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow
import Theorems.Thm_ModularCurve_IsGamma1Link_exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_inLine_level_snd_fst_xP_of_curve_eq_of_level_fst_eq_rigidDataH1Pow
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LinkLineSol

p2m_open "ModularCurve WeierstrassCurve~evalEval_ψ_sq WeierstrassCurve.Affine Polynomial"

variable {K : Type} [Field K] [DecidableEq K]

def xco {W : WeierstrassCurve.Affine K} : W.Point → K
  | 0 => 0
  | .some x _ _ => x

@[scoped simp] theorem xco_some {W : WeierstrassCurve.Affine K} (x y : K) (h : W.Nonsingular x y) :
    xco (Point.some x y h) = x := rfl

theorem xco_neg {W : WeierstrassCurve.Affine K} (P : W.Point) : xco (-P) = xco P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]; rfl

theorem eq_or_eq_neg_of_xco_eq {W : WeierstrassCurve.Affine K} {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : xco P = xco Q) : Q = P ∨ Q = -P := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hP
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hQ
  simp only [xco_some] at h
  subst h
  rcases Y_eq_of_X_eq h₂.left h₁.left rfl with hy | hy
  · left; subst hy; rfl
  · right
    rw [Point.neg_some]
    subst hy; rfl

section Count

variable {W : WeierstrassCurve.Affine K}

theorem nsmul_ne_zero_of_coprime (P : W.Point) {q : ℕ} (hq : 1 < q) (hP : addOrderOf P = q) {n : ℕ}
    (hn : q.Coprime n) : n • P ≠ 0 := by
  intro h0
  have h1 : addOrderOf (n • P) = q := by
    rw [← hP] at hn ⊢; exact hn.addOrderOf_nsmul
  rw [h0, addOrderOf_zero] at h1
  omega

theorem card_fibre_le_two (P : W.Point) {q : ℕ} (hq : 1 < q) (hP : addOrderOf P = q) (b : K) :
    (((Finset.range q).filter (fun n => q.Coprime n)).filter (fun n => xco (n • P) = b)).card ≤ 2 := by
  classical
  set S := ((Finset.range q).filter (fun n => q.Coprime n)).filter (fun n => xco (n • P) = b) with hS
  by_cases hne : S.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hne
    have hsub : S ⊆ ({n₀, q - n₀} : Finset ℕ) := by
      intro m hm
      have hm' := hm
      have hn₀' := hn₀
      simp only [hS, Finset.mem_filter, Finset.mem_range] at hm' hn₀'
      obtain ⟨⟨hmq, hmc⟩, hmb⟩ := hm'
      obtain ⟨⟨hn₀q, hn₀c⟩, hn₀b⟩ := hn₀'
      have hx : xco (n₀ • P) = xco (m • P) := by rw [hmb, hn₀b]
      rcases eq_or_eq_neg_of_xco_eq (nsmul_ne_zero_of_coprime P hq hP hn₀c)
        (nsmul_ne_zero_of_coprime P hq hP hmc) hx with heq | heq
      · have hmod : m ≡ n₀ [MOD addOrderOf P] := nsmul_eq_nsmul_iff_modEq.mp heq
        rw [hP] at hmod
        have : m = n₀ := by
          have := Nat.ModEq.eq_of_lt_of_lt hmod hmq hn₀q
          exact this
        simp [this]
      · have hsum : (m + n₀) • P = 0 := by rw [add_nsmul, heq, neg_add_cancel]
        have hdvd : q ∣ m + n₀ := by
          rw [← hP]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsum
        obtain ⟨c, hc⟩ := hdvd
        have hc1 : c = 1 := by
          have h0 : 0 < m + n₀ := by
            rcases Nat.eq_zero_or_pos n₀ with h | h
            · subst h
              have : q = 1 := by simpa using hn₀c
              omega
            · omega
          have : c < 2 := by nlinarith
          have : 0 < c := by
            rcases Nat.eq_zero_or_pos c with h | h
            · subst h; omega
            · exact h
          omega
        subst hc1
        have : m = q - n₀ := by omega
        simp [this]
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

theorem totient_le_two_mul_card_image (P : W.Point) {q : ℕ} (hq : 1 < q) (hP : addOrderOf P = q) :
    q.totient ≤ 2 * (((Finset.range q).filter (fun n => q.Coprime n)).image (fun n => xco (n • P))).card := by
  classical
  rw [Nat.totient_eq_card_coprime]
  exact Finset.card_le_mul_card_image _ 2 (fun b _ => card_fibre_le_two P hq hP b)

end Count

section Unique

variable {W : WeierstrassCurve K}

theorem natDegree_eq_of_le_of_coeff_eq_one {h : K[X]} {d : ℕ} (h1 : h.natDegree ≤ d) (h2 : h.coeff d = 1) :
    h.natDegree = d :=
  le_antisymm h1 (le_natDegree_of_ne_zero (by rw [h2]; exact one_ne_zero))

theorem eq_prod_of_monic_of_roots (h : K[X]) (hm : h.Monic) (T : Finset K) (hT : ∀ t ∈ T, h.IsRoot t)
    (hdeg : h.natDegree ≤ T.card) : h = ∏ t ∈ T, (X - C t) := by
  classical
  have hdvd : (∏ t ∈ T, (X - C t)) ∣ h := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      exact (pairwise_coprime_X_sub_C (s := fun t : K => t) (fun _ _ h => h)) hab
    · intro t ht
      exact dvd_iff_isRoot.mpr (hT t ht)
  have hmon : (∏ t ∈ T, (X - C t)).Monic := monic_prod_of_monic _ _ fun t _ => monic_X_sub_C t
  have hnat : (∏ t ∈ T, (X - C t)).natDegree = T.card := by
    rw [natDegree_prod_of_monic _ _ fun t _ => monic_X_sub_C t]
    simp
  exact eq_of_monic_of_dvd_of_natDegree_le hmon hm hdvd (by rw [hnat]; exact hdeg)

theorem cyclicGenKernel_unique {p k : ℕ} (hpk : 2 < p ^ k) {h₁ h₂ : K[X]}
    (hh₁ : W.IsCyclicGenKernel p k h₁) (hh₂ : W.IsCyclicGenKernel p k h₂)
    (P : W.toAffine.Point) (hP : addOrderOf P = p ^ k)
    (H₁ : ∀ n : ℕ, (p ^ k).Coprime n → h₁.IsRoot (xco (n • P)))
    (H₂ : ∀ n : ℕ, (p ^ k).Coprime n → h₂.IsRoot (xco (n • P))) : h₁ = h₂ := by
  classical
  set T := ((Finset.range (p ^ k)).filter (fun n => (p ^ k).Coprime n)).image (fun n => xco (n • P)) with hT
  have hcard : (p ^ k).totient ≤ 2 * T.card := totient_le_two_mul_card_image P (by omega) hP
  obtain ⟨e, he⟩ := Nat.totient_even hpk
  have hd : (p ^ k).totient / 2 ≤ T.card := by omega
  have hroots : ∀ (h : K[X]), (∀ n : ℕ, (p ^ k).Coprime n → h.IsRoot (xco (n • P))) → ∀ t ∈ T, h.IsRoot t := by
    intro h H t ht
    simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨n, ⟨-, hn⟩, rfl⟩ := ht
    exact H n hn
  have hdeg₁ := natDegree_eq_of_le_of_coeff_eq_one hh₁.natDegree_le hh₁.coeff_eq_one
  have hdeg₂ := natDegree_eq_of_le_of_coeff_eq_one hh₂.natDegree_le hh₂.coeff_eq_one
  rw [eq_prod_of_monic_of_roots h₁ (hh₁.monic W) T (hroots h₁ H₁) (by rw [hdeg₁]; exact hd),
    eq_prod_of_monic_of_roots h₂ (hh₂.monic W) T (hroots h₂ H₂) (by rw [hdeg₂]; exact hd)]

theorem twoKernel_unique {h₁ h₂ : K[X]} (hh₁ : W.IsTwoKernel h₁) (hh₂ : W.IsTwoKernel h₂) (a : K)
    (H₁ : h₁.IsRoot a) (H₂ : h₂.IsRoot a) : h₁ = h₂ := by
  have e₁ := eq_X_add_C_of_natDegree_le_one hh₁.natDegree_le
  have e₂ := eq_X_add_C_of_natDegree_le_one hh₂.natDegree_le
  rw [hh₁.coeff_eq_one, map_one, one_mul] at e₁
  rw [hh₂.coeff_eq_one, map_one, one_mul] at e₂
  have r₁ : h₁.coeff 0 = -a := by
    have := H₁; rw [e₁, IsRoot, eval_add, eval_X, eval_C] at this; linear_combination this
  have r₂ : h₂.coeff 0 = -a := by
    have := H₂; rw [e₂, IsRoot, eval_add, eval_X, eval_C] at this; linear_combination this
  rw [e₁, e₂, r₁, r₂]

theorem gamma0PowAt_unique {p k M : ℕ} (hp : p.Prime) (hk : 0 < k) (hM : M ≠ 0) (hdvd : p ^ k ∣ M) {h₁ h₂ : K[X]}
    (hh₁ : IsGamma0PowAt W p k h₁) (hh₂ : IsGamma0PowAt W p k h₂)
    (g : W.toAffine.Point) (hg : addOrderOf g = M)
    (H₁ : ∀ (n : ℕ) (x₁ y₁ : K) (hxy : W.toAffine.Nonsingular x₁ y₁),
      n • g = Point.some x₁ y₁ hxy → addOrderOf (n • g) = p ^ k → h₁.IsRoot x₁)
    (H₂ : ∀ (n : ℕ) (x₁ y₁ : K) (hxy : W.toAffine.Nonsingular x₁ y₁),
      n • g = Point.some x₁ y₁ hxy → addOrderOf (n • g) = p ^ k → h₂.IsRoot x₁) : h₁ = h₂ := by
  classical

  set P : W.toAffine.Point := (M / p ^ k) • g with hPdef
  have hP : addOrderOf P = p ^ k := by
    rw [hPdef, ← hg]
    exact addOrderOf_nsmul_addOrderOf_sub (by rw [hg]; exact hM) (by rw [hg]; exact hdvd)
  have hpk1 : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt

  have key : ∀ (h : K[X]), (∀ (n : ℕ) (x₁ y₁ : K) (hxy : W.toAffine.Nonsingular x₁ y₁),
      n • g = Point.some x₁ y₁ hxy → addOrderOf (n • g) = p ^ k → h.IsRoot x₁) →
      ∀ n : ℕ, (p ^ k).Coprime n → h.IsRoot (xco (n • P)) := by
    intro h H n hn
    have hord : addOrderOf (n • P) = p ^ k := by
      rw [← hP] at hn ⊢; exact hn.addOrderOf_nsmul
    have hne : n • P ≠ 0 := nsmul_ne_zero_of_coprime P hpk1 hP hn
    have hmul : n • P = (n * (M / p ^ k)) • g := by rw [hPdef, mul_nsmul']
    rcases hQ : n • P with _ | ⟨x₁, y₁, hxy⟩
    · exact absurd hQ hne
    · rw [xco_some]
      refine H (n * (M / p ^ k)) x₁ y₁ hxy (by rw [← hmul, hQ]) ?_
      rw [← hmul, hord]
  by_cases h2 : p ^ k = 2
  · rw [isGamma0PowAt_of_pow_eq_two W h2] at hh₁ hh₂
    have c1 : (p ^ k).Coprime 1 := Nat.coprime_one_right _
    have r₁ := key h₁ H₁ 1 c1
    have r₂ := key h₂ H₂ 1 c1
    exact twoKernel_unique hh₁ hh₂ _ r₁ r₂
  · rw [isGamma0PowAt_of_pow_ne_two W h2] at hh₁ hh₂
    have hpk : 2 < p ^ k := by omega
    exact cyclicGenKernel_unique hpk hh₁ hh₂ P hP (key h₁ H₁) (key h₂ H₂)

end Unique

section Extra

variable (W : WeierstrassCurve K)

theorem evalEval_ψ_sq (n : ℤ) {x y : K} (hxy : W.toAffine.Equation x y) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have h1 : (Affine.CoordinateRing.mk W) ((W.ψ n) ^ 2) = (Affine.CoordinateRing.mk W) (C (W.ΨSq n)) := by
    rw [map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨r, hr⟩ := (AdjoinRoot.mk_eq_mk).mp h1
  have h2 := congrArg (Polynomial.evalEval x y) hr
  rw [evalEval_sub, evalEval_pow, evalEval_C, evalEval_mul] at h2
  have h3 : Polynomial.evalEval x y (WeierstrassCurve.Affine.polynomial W) = 0 := hxy
  rw [h3, zero_mul, sub_eq_zero] at h2
  exact h2

theorem eval_ΨSq_ne_zero_of_zsmul_ne_zero [W.IsElliptic] (n : ℤ) {x y : K} (hxy : W.toAffine.Nonsingular x y)
    (hn : n • (Point.some x y hxy : W.toAffine.Point) ≠ 0) : (W.ΨSq n).eval x ≠ 0 := by
  intro h0
  apply hn
  rw [WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W hxy n]
  have := evalEval_ψ_sq W n hxy.left
  rw [h0] at this
  exact pow_eq_zero_iff two_ne_zero |>.mp this

variable {W}

theorem exists_coprime_eq_nsmul_or_eq_neg {p k : ℕ} (hpk : 2 < p ^ k) {h : K[X]}
    (hh : W.IsCyclicGenKernel p k h) (P : W.toAffine.Point) (hP : addOrderOf P = p ^ k)
    (H : ∀ n : ℕ, (p ^ k).Coprime n → h.IsRoot (xco (n • P)))
    (Q : W.toAffine.Point) (hQ0 : Q ≠ 0) (hQ : h.IsRoot (xco Q)) :
    ∃ n : ℕ, (p ^ k).Coprime n ∧ (Q = n • P ∨ Q = -(n • P)) := by
  classical
  set T := ((Finset.range (p ^ k)).filter (fun n => (p ^ k).Coprime n)).image (fun n => xco (n • P)) with hT
  have hcard : (p ^ k).totient ≤ 2 * T.card := totient_le_two_mul_card_image P (by omega) hP
  obtain ⟨e, he⟩ := Nat.totient_even hpk
  have hd : (p ^ k).totient / 2 ≤ T.card := by omega
  have hroots : ∀ t ∈ T, h.IsRoot t := by
    intro t ht
    simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨n, ⟨-, hn⟩, rfl⟩ := ht
    exact H n hn
  have hdeg := natDegree_eq_of_le_of_coeff_eq_one hh.natDegree_le hh.coeff_eq_one
  have hprod := eq_prod_of_monic_of_roots h (hh.monic W) T hroots (by rw [hdeg]; exact hd)
  have hmem : xco Q ∈ T := by
    have h0 : (∏ t ∈ T, (X - C t)).eval (xco Q) = 0 := by rw [← hprod]; exact hQ
    rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨t, ht, h0⟩ := h0
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at h0
    rw [h0]; exact ht
  simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hmem
  obtain ⟨n, ⟨-, hn⟩, hnx⟩ := hmem
  exact ⟨n, hn, eq_or_eq_neg_of_xco_eq (nsmul_ne_zero_of_coprime P (by omega) hP hn) hQ0 hnx⟩

end Extra

end LinkLineSol
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_inLine_level_snd_fst_xP_of_curve_eq_of_level_fst_eq_rigidDataH1Pow.LinkLineSol"

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel LinkLineSol in
open scoped Classical in
theorem solution
    (A : Type) [CommRing A] (ℓg M' q : ℕ) [NeZero M']
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (κ : Type) [Field κ] [IsAlgClosed κ] [DecidableEq κ] [Algebra A κ] (hM'κ : ((M' : ℕ) : κ) ≠ 0)
    (hℓg : ℓg.Prime) (hℓg2 : ℓg ≠ 2) (hℓgM' : ℓg ∣ M')
    (x x' : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw κ)
    (hc : x.curve = x'.curve) (ht : x.level.1 = x'.level.1) :
    ModularCurve.InLine x'.curve ℓg x'.level.2.1.xP x.level.2.1.xP := by
  classical
  haveI hFact : Fact ℓg.Prime := ⟨hℓg⟩

  have hM0 : M' ≠ 0 := NeZero.ne M'
  have hmem : ℓg ∈ M'.primeFactors := Nat.mem_primeFactors.mpr ⟨hℓg, hℓgM', hM0⟩
  have hℓ3 : 3 ≤ ℓg := by
    have h2 := hℓg.two_le
    omega
  have hℓκ : ((ℓg : ℕ) : κ) ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := hℓgM'
    apply hM'κ
    rw [hc]; push_cast; rw [h0, zero_mul]
  set k : ℕ := M'.factorization ℓg with hk
  have hkpos : 0 < k := hℓg.factorization_pos_of_dvd hM0 hℓgM'
  have hdvd : ℓg ^ k ∣ M' := Nat.ordProj_dvd M' _
  have hpk1 : 1 < ℓg ^ k := Nat.one_lt_pow hkpos.ne' hℓg.one_lt
  have hpk2 : 2 < ℓg ^ k := by
    have : ℓg ≤ ℓg ^ k := by
      calc ℓg = ℓg ^ 1 := (pow_one ℓg).symm
        _ ≤ ℓg ^ k := Nat.pow_le_pow_right hℓg.pos hkpos
    omega

  obtain ⟨W₀, hΔ₀, lev, hlev⟩ := x
  dsimp only at hc ht ⊢
  subst hc
  set W := x'.curve with hWdef
  have hΔ : IsUnit W.Δ := x'.isUnit_Δ
  haveI hE : W.IsElliptic := ⟨hΔ⟩
  set h : ↥M'.primeFactors → Polynomial κ := x'.level.1 with hhdef
  have hh : ∀ p : ↥M'.primeFactors, IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (h p) := x'.isLevel.1.1
  have hhℓ : W.IsCyclicGenKernel ℓg k (h ⟨ℓg, hmem⟩) := by
    have := hh ⟨ℓg, hmem⟩
    rwa [isGamma0PowAt_of_pow_ne_two W (by omega : ℓg ^ k ≠ 2)] at this

  set D' : LevelPData κ := x'.level.2.1 with hD'
  set D : LevelPData κ := lev.2.1 with hD
  have hDpt' : IsGamma1Point W ℓg D' := x'.isLevel.1.2.1
  have hDpt : IsGamma1Point W ℓg D := hlev.1.2.1
  have hlink' : IsGamma1Link W ℓg M' h D' := x'.isLevel.2
  have hlink : IsGamma1Link W ℓg M' h D := by rw [← ht]; exact hlev.2
  obtain ⟨xG', yG', hG'eq, hG'root, hP'⟩ :=
    ModularCurve.IsGamma1Link.exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed ℓg M' hℓ3 hℓκ hmem W hΔ h hh D' hDpt' hlink'
  obtain ⟨xG, yG, hGeq, hGroot, hP⟩ :=
    ModularCurve.IsGamma1Link.exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed ℓg M' hℓ3 hℓκ hmem W hΔ h hh D hDpt hlink

  have nG' : W.toAffine.Nonsingular xG' yG' := W.toAffine.equation_iff_nonsingular.mp hG'eq
  have nG : W.toAffine.Nonsingular xG yG := W.toAffine.equation_iff_nonsingular.mp hGeq
  have nP' : W.toAffine.Nonsingular D'.xP D'.yP := W.toAffine.equation_iff_nonsingular.mp hDpt'.equation_P
  have nP : W.toAffine.Nonsingular D.xP D.yP := W.toAffine.equation_iff_nonsingular.mp hDpt.equation_P
  have htoG' : (ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) xG' yG' : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some xG' yG' nG' := dif_pos nG'
  have htoG : (ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) xG yG : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some xG yG nG := dif_pos nG
  have htoP' : (ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) D'.xP D'.yP : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some D'.xP D'.yP nP' := dif_pos nP'
  have htoP : (ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) D.xP D.yP : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some D.xP D.yP nP := dif_pos nP
  set N : ℕ := ℓg ^ (k - 1) with hN
  have hP'pt : (WeierstrassCurve.Affine.Point.some D'.xP D'.yP nP' : W.toAffine.Point) =
      N • WeierstrassCurve.Affine.Point.some xG' yG' nG' := by
    have := hP'
    rw [← htoP', ← htoG']; exact this
  have hPpt : (WeierstrassCurve.Affine.Point.some D.xP D.yP nP : W.toAffine.Point) =
      N • WeierstrassCurve.Affine.Point.some xG yG nG := by
    have := hP
    rw [← htoP, ← htoG]; exact this

  obtain ⟨g, hgo, hgr⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow
      A ℓg M' q hℓ hM hL 𝒢 𝒯 κ hM'κ x'
  set Pℓ : W.toAffine.Point := (M' / ℓg ^ k) • g with hPℓ
  have hPℓord : addOrderOf Pℓ = ℓg ^ k := by
    have hq : M' / ℓg ^ k = addOrderOf g / ℓg ^ k := by rw [hgo]
    rw [hPℓ, hq]
    exact addOrderOf_nsmul_addOrderOf_sub (by rw [hgo]; exact hM0) (by rw [hgo]; exact hdvd)
  have key : ∀ n : ℕ, (ℓg ^ k).Coprime n → (h ⟨ℓg, hmem⟩).IsRoot (xco (n • Pℓ)) := by
    intro n hn
    have hord : addOrderOf (n • Pℓ) = ℓg ^ k := by
      rw [← hPℓord] at hn ⊢; exact hn.addOrderOf_nsmul
    have hne : n • Pℓ ≠ 0 := nsmul_ne_zero_of_coprime Pℓ hpk1 hPℓord hn
    have hmul : n • Pℓ = (n * (M' / ℓg ^ k)) • g := by rw [hPℓ, mul_nsmul']
    rcases hQ : n • Pℓ with _ | ⟨x₁, y₁, hxy⟩
    · exact absurd hQ hne
    · rw [xco_some]
      refine hgr ⟨ℓg, hmem⟩ (n * (M' / ℓg ^ k)) x₁ y₁ hxy (by rw [← hmul, hQ]) ?_
      rw [← hmul, hord]

  obtain ⟨n', hn', hG'⟩ := exists_coprime_eq_nsmul_or_eq_neg hpk2 hhℓ Pℓ hPℓord key
    (WeierstrassCurve.Affine.Point.some xG' yG' nG') (WeierstrassCurve.Affine.Point.some_ne_zero _)
    (by rw [xco_some]; exact hG'root)
  obtain ⟨n, hn, hG⟩ := exists_coprime_eq_nsmul_or_eq_neg hpk2 hhℓ Pℓ hPℓord key
    (WeierstrassCurve.Affine.Point.some xG yG nG) (WeierstrassCurve.Affine.Point.some_ne_zero _)
    (by rw [xco_some]; exact hGroot)

  set R : W.toAffine.Point := N • Pℓ with hR
  have hNeq : ℓg ^ k / ℓg = N := by
    rw [hN]
    exact Nat.div_eq_of_eq_mul_left hℓg.pos (by rw [← pow_succ, Nat.sub_add_cancel hkpos])
  have hRord : addOrderOf R = ℓg := by
    have hN' : N = addOrderOf Pℓ / ℓg := by rw [hPℓord, hNeq]
    rw [hR, hN']
    exact addOrderOf_nsmul_addOrderOf_sub (by rw [hPℓord]; exact pow_ne_zero _ hℓg.ne_zero)
      (by rw [hPℓord]; exact dvd_pow_self ℓg hkpos.ne')
  have hℓR : ℓg • R = 0 := by rw [← hRord]; exact addOrderOf_nsmul_eq_zero R

  have pm_nsmul : ∀ (m : ℕ) (A B : W.toAffine.Point), (A = B ∨ A = -B) → (m • A = m • B ∨ m • A = -(m • B)) := by
    rintro m A B (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (neg_nsmul B m ▸ rfl)
  have pm_trans : ∀ (A B C : W.toAffine.Point), (A = B ∨ A = -B) → (B = C ∨ B = -C) → (A = C ∨ A = -C) := by
    rintro A B C (rfl | rfl) (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg C)
  have pm_symm : ∀ (A B : W.toAffine.Point), (A = B ∨ A = -B) → (B = A ∨ B = -A) := by
    rintro A B (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (neg_neg B).symm

  set S' : W.toAffine.Point := WeierstrassCurve.Affine.Point.some D'.xP D'.yP nP' with hS'
  set S : W.toAffine.Point := WeierstrassCurve.Affine.Point.some D.xP D.yP nP with hS
  have hS'R : S' = n' • R ∨ S' = -(n' • R) := by
    have h1 := pm_nsmul N _ _ hG'
    rw [← hP'pt, ← mul_nsmul', mul_comm, mul_nsmul'] at h1
    exact h1
  have hSR : S = n • R ∨ S = -(n • R) := by
    have h1 := pm_nsmul N _ _ hG
    rw [← hPpt, ← mul_nsmul', mul_comm, mul_nsmul'] at h1
    exact h1

  have hcop' : ℓg.Coprime n' := Nat.Coprime.coprime_dvd_left (dvd_pow_self ℓg hkpos.ne') hn'
  have hcop : ℓg.Coprime n := Nat.Coprime.coprime_dvd_left (dvd_pow_self ℓg hkpos.ne') hn
  haveI : Fact (1 < ℓg) := ⟨hℓg.one_lt⟩
  have hn'0 : ((n' : ℕ) : ZMod ℓg) ≠ 0 := by
    intro h0
    have hdn : ℓg ∣ n' := (CharP.cast_eq_zero_iff (ZMod ℓg) ℓg n').mp h0
    exact hℓg.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop' hdn)
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, n' * m' % ℓg = 1 := by
    refine ⟨((n' : ZMod ℓg)⁻¹).val, ?_⟩
    have h1 : (((n' * ((n' : ZMod ℓg)⁻¹).val : ℕ)) : ZMod ℓg) = 1 := by
      push_cast
      rw [ZMod.natCast_zmod_val, mul_inv_cancel₀ hn'0]
    have h2 := congrArg ZMod.val h1
    rwa [ZMod.val_natCast, ZMod.val_one] at h2
  have hmodR : ∀ t : ℕ, (t % ℓg) • R = t • R := fun t => by rw [← hRord]; exact mod_addOrderOf_nsmul R t
  have hm'S' : m' • S' = R ∨ m' • S' = -R := by
    have h1 := pm_nsmul m' _ _ hS'R
    rw [← mul_nsmul', mul_comm, ← hmodR (n' * m'), hm', one_nsmul] at h1
    exact h1

  have hSc : S = (n * m') • S' ∨ S = -((n * m') • S') := by
    have h1 : n • R = (n * m') • S' ∨ n • R = -((n * m') • S') := by
      rcases hm'S' with h | h
      · left; rw [← h, smul_smul]
      · right; rw [show R = -(m' • S') by rw [h, neg_neg], smul_neg, smul_smul]
    exact pm_trans _ _ _ hSR h1

  have hS'ord : addOrderOf S' = ℓg := by
    have h1 : addOrderOf (n' • R) = ℓg := by
      rw [← hRord] at hcop' ⊢; exact hcop'.addOrderOf_nsmul
    rcases hS'R with h | h
    · rw [h, h1]
    · rw [h, addOrderOf_neg, h1]
  have hℓS' : ℓg • S' = 0 := by rw [← hS'ord]; exact addOrderOf_nsmul_eq_zero S'
  have hmodS' : ∀ t : ℕ, (t % ℓg) • S' = t • S' := fun t => by rw [← hS'ord]; exact mod_addOrderOf_nsmul S' t

  set c : ℕ := n * m' with hc
  have hcop'' : ℓg.Coprime c := by
    rw [hc]
    refine Nat.Coprime.mul_right hcop ?_

    rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]
    have : Nat.gcd m' ℓg ∣ 1 := by
      have hd1 : Nat.gcd m' ℓg ∣ n' * m' % ℓg := by
        exact (Nat.dvd_mod_iff (Nat.gcd_dvd_right _ _)).mpr (Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) _)
      rwa [hm'] at hd1
    exact Nat.dvd_one.mp this
  set r : ℕ := c % ℓg with hr
  have hrpos : 0 < r := by
    rw [hr]
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have hdc : ℓg ∣ c := Nat.dvd_of_mod_eq_zero h0
    have : ℓg = 1 := Nat.Coprime.eq_one_of_dvd hcop'' (by simpa using hdc)
    exact hℓg.one_lt.ne' this
  have hrlt : r < ℓg := by rw [hr]; exact Nat.mod_lt _ hℓg.pos
  have hodd : ℓg % 2 = 1 := Nat.odd_iff.mp (hℓg.odd_of_ne_two hℓg2)
  set a : ℕ := if r ≤ (ℓg - 1) / 2 then r else ℓg - r with ha
  have ha1 : 1 ≤ a := by rw [ha]; split_ifs <;> omega
  have ha2 : a ≤ (ℓg - 1) / 2 := by rw [ha]; split_ifs <;> omega
  have haS' : a • S' = c • S' ∨ a • S' = -(c • S') := by
    rw [ha]
    split_ifs with hle
    · left; rw [hr, hmodS']
    · right
      have h1 : (ℓg - r) • S' + r • S' = 0 := by
        rw [← add_nsmul, Nat.sub_add_cancel hrlt.le, hℓS']
      rw [eq_neg_of_add_eq_zero_left h1, hr, hmodS']
  have haS : a • S' = S ∨ a • S' = -S := pm_trans _ _ _ haS' (pm_symm _ _ hSc)

  have hane : ((a : ℕ) : ℤ) • S' ≠ 0 := by
    rw [natCast_zsmul]
    rcases haS with h | h
    · rw [h]; exact WeierstrassCurve.Affine.Point.some_ne_zero _
    · rw [h, neg_ne_zero]; exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have hψ : (W.ψ (a : ℤ)).evalEval D'.xP D'.yP ≠ 0 := fun h0 =>
    hane ((WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W nP' (a : ℤ)).mpr h0)
  have hΨ : (W.ΨSq (a : ℤ)).eval D'.xP ≠ 0 := eval_ΨSq_ne_zero_of_zsmul_ne_zero W (a : ℤ) nP' hane
  obtain ⟨y'', h'', hmul⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div W nP' (n := (a : ℤ)) hψ
  rw [natCast_zsmul] at hmul
  have hx : (W.Φ (a : ℤ)).eval D'.xP / (W.ΨSq (a : ℤ)).eval D'.xP = D.xP := by
    rcases haS with h | h
    · rw [h, hS] at hmul
      exact ((WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hmul.symm).1
    · rw [h, hS, WeierstrassCurve.Affine.Point.neg_some] at hmul
      exact ((WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hmul.symm).1
  refine ⟨a, ha1, ha2, ?_⟩
  rw [← hx, div_mul_cancel₀ _ hΨ]

#print axioms solution

end S_WeierstrassCurve_DrinfeldGlobal_inLine_level_snd_fst_xP_of_curve_eq_of_level_fst_eq_rigidDataH1Pow
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_inLine_level_snd_fst_xP_of_curve_eq_of_level_fst_eq_rigidDataH1Pow (solution)
