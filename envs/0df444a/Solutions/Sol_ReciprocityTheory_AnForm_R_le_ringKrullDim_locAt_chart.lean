-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.le_ringKrullDim_locAt_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:34.505872+00:00
-- url     : https://prove2.me/submissions/dfd9b7a3-0cb7-46b8-9b4c-d4876c830a27

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Theorems.Thm_ReciprocityTheory_AnForm_R_chartIdeal_le_ptIdealOf
import Theorems.Thm_ReciprocityTheory_AnForm_R_ptIdealOf_isMaximal
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_locAt
import Theorems.Thm_ReciprocityTheory_CA_exists_dim_trdeg_field
import Theorems.Thm_ReciprocityTheory_CA_height_eq_of_isMaximal_of_trdeg_eq_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
set_option maxHeartbeats 600000
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ h ∈ chartIdeal P p, eval z h = 0) :
    (e : WithBot ℕ∞) ≤ ringKrullDim (locAt (chartIdeal P p) z) := by
  have hIm : chartIdeal P p ≤ ptIdealOf z := chartIdeal_le_ptIdealOf hz
  have hPm : P ≤ ptIdealOf z := le_sup_left.trans hIm
  have := ptIdealOf_isMaximal z
  obtain ⟨Q, hQmin, hQm⟩ := Ideal.exists_minimalPrimes_le hPm
  have hQp : Q.IsPrime := hQmin.1.1
  have hPQ : P ≤ Q := hQmin.1.2
  have : IsDomain (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) := Ideal.Quotient.isDomain Q
  have : Algebra.FiniteType ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ Q) (Ideal.Quotient.mkₐ_surjective ℂ Q)
  obtain ⟨s, hsd, hst⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Σ k, ι k) ℂ ⧸ Q)
  have hs : s = e + Fintype.card K := by
    have h := hdim Q hQmin
    rw [hsd] at h
    exact_mod_cast h
  have hmQ : ((ptIdealOf z).map (Ideal.Quotient.mk Q)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk Q)
      Ideal.Quotient.mk_surjective (ptIdealOf_isMaximal z) with h | h
    · exfalso
      have h1 : Ideal.Quotient.mk Q 1 ∈ (ptIdealOf z).map (Ideal.Quotient.mk Q) := by
        rw [h]; exact Submodule.mem_top
      exact (ptIdealOf_isMaximal z).ne_top
        ((Ideal.eq_top_iff_one _).mpr ((Ideal.mem_quotient_iff_mem hQm).mp h1))
    · exact h
  have hhtQ : ((ptIdealOf z).map (Ideal.Quotient.mk Q)).height = ((e + Fintype.card K : ℕ) : ℕ∞) := by
    rw [← hs]
    exact ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field (K := ℂ) s hst _
  have hdQ : ringKrullDim (locAt Q z) = (((e + Fintype.card K : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [ringKrullDim_locAt Q z hQm, hhtQ]
  have hPQd : ringKrullDim (locAt Q z) ≤ ringKrullDim (locAt P z) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor (Ideal.map_mono hPQ))
      (Ideal.Quotient.factor_surjective _)

  let J : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
    Ideal.span (Set.range fun k => (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ))
  obtain ⟨sset, hsset⟩ : ∃ s : Set (MvPolynomial (Σ k, ι k) ℂ ⧸ P), s = Ideal.Quotient.mk P ''
      Set.range (fun k => (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ)) := ⟨_, rfl⟩
  have hmP : ((ptIdealOf z).map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPm)
  have hsub : sset ⊆ (ptIdealOf z).map (Ideal.Quotient.mk P) := by
    rw [hsset]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact Ideal.mem_map_of_mem _ (hIm (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)))
  have hH := Ideal.height_le_height_add_encard_of_subset sset hsub
  have hspan : Ideal.span sset = J.map (Ideal.Quotient.mk P) := by
    rw [hsset, Ideal.map_span]
  let eq2 : (MvPolynomial (Σ k, ι k) ℂ ⧸ P) ⧸ Ideal.span sset ≃+* MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p :=
    (Ideal.quotEquivOfEq hspan).trans (DoubleQuot.quotQuotEquivQuotSup P J)
  have hcomp : (eq2 : _ →+* _).comp ((Ideal.Quotient.mk (Ideal.span sset)).comp (Ideal.Quotient.mk P)) =
      Ideal.Quotient.mk (chartIdeal P p) := by
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, eq2, RingEquiv.coe_toRingHom]
    exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk P J a
  have hht : ((ptIdealOf z).map (Ideal.Quotient.mk (chartIdeal P p))).height =
      (((ptIdealOf z).map (Ideal.Quotient.mk P)).map (Ideal.Quotient.mk (Ideal.span sset))).height := by
    have hmap : (((ptIdealOf z).map (Ideal.Quotient.mk P)).map
        (Ideal.Quotient.mk (Ideal.span sset))).map eq2 =
        (ptIdealOf z).map (Ideal.Quotient.mk (chartIdeal P p)) := by
      have h : (((ptIdealOf z).map (Ideal.Quotient.mk P)).map
          (Ideal.Quotient.mk (Ideal.span sset))).map (eq2 : _ →+* _) =
          (ptIdealOf z).map (Ideal.Quotient.mk (chartIdeal P p)) := by
        rw [Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, hcomp]
      exact h
    rw [← hmap, RingEquiv.height_map]
  have henc : sset.encard ≤ Fintype.card K := by
    rw [hsset]
    refine (Set.encard_image_le (Ideal.Quotient.mk P) _).trans ?_
    rw [← Set.image_univ]
    refine (Set.encard_image_le _ _).trans ?_
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
  have h1 : ((e + Fintype.card K : ℕ) : ℕ∞) ≤ ((ptIdealOf z).map (Ideal.Quotient.mk P)).height := by
    have h := hPQd
    rw [hdQ, ringKrullDim_locAt P z hPm] at h
    exact_mod_cast h
  have h2 : ((ptIdealOf z).map (Ideal.Quotient.mk P)).height ≤
      ((ptIdealOf z).map (Ideal.Quotient.mk (chartIdeal P p))).height + Fintype.card K := by
    rw [hht]
    exact hH.trans (by gcongr)
  have h3 : (e : ℕ∞) ≤ ((ptIdealOf z).map (Ideal.Quotient.mk (chartIdeal P p))).height := by
    have h4 := h1.trans h2
    rw [Nat.cast_add, add_comm, add_comm _ (Fintype.card K : ℕ∞)] at h4
    exact ENat.addLECancellable_of_ne_top (ENat.natCast_ne_top _) h4
  rw [ringKrullDim_locAt _ z hIm]
  exact_mod_cast h3
end ReciprocityTheory.AnForm.R
