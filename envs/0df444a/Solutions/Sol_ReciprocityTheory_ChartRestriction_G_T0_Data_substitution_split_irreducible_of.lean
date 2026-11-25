-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.substitution_split_irreducible_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:09:43.885437+00:00
-- url     : https://prove2.me/submissions/020514a2-80f9-4947-a173-6a6c5a3e10af

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PowFirstVarDvdSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvalOneBilinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionSplitIrreducibleOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_wt_isX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_wt_isU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_weightGrading_substitution
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_psiX_g
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_psiU_g
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_eq_monomial_of_dehomog_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_pow_first_var_dvd_substitution
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_evalOne_bilinearSubstitution
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_irreducible_theta_rename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_WH_hom_of_dvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_WH_hom_of_psiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_WH_wt_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_WH_wt_single


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (c : ι) (F0 : KTp K d.D d.N) (hirr : Irreducible F0) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) :
    ∃ (a : ℕ) (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (deF : ℕ),
      bilinearSubstitution F0 = X (Sum.inr 0) ^ a * F1 ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧ deF ≤ d0 ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d0) := by
  classical
  have hF0 : F0 ≠ 0 := hirr.ne_zero
  have hirr1 : Irreducible (LinearSubstitution.ev1 (bilinearSubstitution F0)) := by
    rw [LinearSubstitution.evalOne_bilinearSubstitution]
    exact LinearSubstitution.irreducible_theta_rename F0 hirr
  have hg0 : bilinearSubstitution F0 ≠ 0 := fun h => hirr1.ne_zero (by rw [h, map_zero])
  have hX : ∀ s ∈ (bilinearSubstitution F0).support, WH.wt LinearSubstitution.isX s = (d.D + 1) * d0 :=
    WH.hom_of_psiP LinearSubstitution.isX _ _ (LinearSubstitution.weightGrading_substitution LinearSubstitution.isX LinearSubstitution.psiX_g F0 d0 hmh)
  have hU : ∀ s ∈ (bilinearSubstitution F0).support, WH.wt LinearSubstitution.isU s = (d.D + 1) * d0 :=
    WH.hom_of_psiP LinearSubstitution.isU _ _ (LinearSubstitution.weightGrading_substitution LinearSubstitution.isU LinearSubstitution.psiU_g F0 d0 hmh)
  have hev : LinearSubstitution.ev1 (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) = 1 := by simp [LinearSubstitution.ev1]
  have hbound : ∀ a, (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0 →
      a ≤ (bilinearSubstitution F0).totalDegree := by
    rintro a ⟨h, hh⟩
    have hh0 : h ≠ 0 := by
      rintro rfl
      exact hg0 (by rw [hh, mul_zero])
    rw [hh, totalDegree_mul_of_isDomain (pow_ne_zero _ (X_ne_zero _)) hh0, totalDegree_X_pow]
    omega
  obtain ⟨a, hPa, hle, hnot⟩ : ∃ a, (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0 ∧
      d.D * d0 ≤ a ∧ ¬ (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ (a + 1) ∣ bilinearSubstitution F0 := by
    have hP0 := d.pow_first_var_dvd_substitution c F0 hF0 hker d0 hmh
    exact ⟨Nat.findGreatest (fun a => (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0)
      (bilinearSubstitution F0).totalDegree,
      Nat.findGreatest_spec (P := fun a => (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0)
        (hbound _ hP0) hP0,
      Nat.le_findGreatest (P := fun a => (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0)
        (hbound _ hP0) hP0,
      fun h => Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hbound _ h) h⟩
  obtain ⟨F1, hF1⟩ := hPa
  have hF10 : F1 ≠ 0 := by
    rintro rfl
    exact hg0 (by rw [hF1, mul_zero])
  have hev1 : LinearSubstitution.ev1 (bilinearSubstitution F0) = LinearSubstitution.ev1 F1 := by
    rw [hF1, map_mul, map_pow, hev, one_pow, one_mul]
  have hdvdF1 : F1 ∣ bilinearSubstitution F0 := ⟨X (Sum.inr 0) ^ a, by rw [hF1, mul_comm]⟩
  obtain ⟨deF, hdeF⟩ := WH.hom_of_dvd LinearSubstitution.isX ((d.D + 1) * d0) (bilinearSubstitution F0) F1 hg0 hX hdvdF1
  have hshift : ∀ s ∈ F1.support, s + Finsupp.single (Sum.inr 0) a ∈ (bilinearSubstitution F0).support := by
    intro s hs
    rw [mem_support_iff, hF1, mul_comm, X_pow_eq_monomial, coeff_mul_monomial, mul_one]
    exact mem_support_iff.1 hs
  refine ⟨a, F1, deF, hF1, ⟨fun hu => ?_, fun G H hGH => ?_⟩, ?_, ?_, ?_⟩
  · exact hirr1.not_isUnit (by rw [hev1]; exact hu.map _)
  · have hmul : LinearSubstitution.ev1 (bilinearSubstitution F0) = LinearSubstitution.ev1 G * LinearSubstitution.ev1 H := by rw [hev1, hGH, map_mul]
    have key : ∀ G' : MvPolynomial (LinearSubstitution.V d.D d.N) K, G' ∣ F1 → IsUnit (LinearSubstitution.ev1 G') → IsUnit G' := by
      intro G' hG' hu
      obtain ⟨k, hk, hkG⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hu
      obtain ⟨m, hm⟩ := WH.hom_of_dvd LinearSubstitution.isX _ (bilinearSubstitution F0) G' hg0 hX (hG'.trans hdvdF1)
      have hG'eq := LinearSubstitution.eq_monomial_of_dehomog_const G' m hm k hkG
      cases m with
      | zero =>
        rw [hG'eq, pow_zero, mul_one]
        exact hk.map C
      | succ m =>
        exfalso
        apply hnot
        obtain ⟨Q, hQ⟩ := hG'
        refine ⟨C k * X (Sum.inr 0) ^ m * Q, ?_⟩
        rw [hF1, hQ, hG'eq]
        ring
    rcases hirr1.isUnit_or_isUnit hmul with h | h
    · exact Or.inl (key G ⟨H, hGH⟩ h)
    · exact Or.inr (key H ⟨G, by rw [hGH, mul_comm]⟩ h)
  · intro s hs
    rw [← LinearSubstitution.wt_isX]
    exact hdeF s hs
  · obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.1 hF10
    have hs' : s ∈ F1.support := mem_support_iff.2 hs
    have h := hX _ (hshift s hs')
    rw [WH.wt_add, WH.wt_single, if_pos (show LinearSubstitution.isX (Sum.inr 0 : LinearSubstitution.V d.D d.N) from rfl),
      hdeF s hs'] at h
    have h2 : (d.D + 1) * d0 = d.D * d0 + d0 := by ring
    linarith
  · intro s hs
    have h := hU _ (hshift s hs)
    rw [WH.wt_add, WH.wt_single, if_neg (by simp [LinearSubstitution.isU]), add_zero] at h
    rw [← LinearSubstitution.wt_isU]
    exact h.le
end ReciprocityTheory.ChartRestriction.G.T0.Data
