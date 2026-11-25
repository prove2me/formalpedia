-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__class_count_plane_bound_5fa37ee7825f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:38:09.275796+00:00
-- url     : https://prove2.me/submissions/3d8e1ea4-9a2f-4c18-a59b-7df5a27cc60b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__boundedIntegers_finite_card_le_8ec145ace085
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__card_submodules_quotient_le_89e4f83fcf5a
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__eq_zero_of_inner_self_eq_zero_e038a7e1209d
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__finrank_orthonormal_plane_eq_two_4d6f147f5377
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__scaledFreeModule_le_comap_78a7cdd93a48
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__isometric_of_orthogonal_pairs_8df74ab90f8e
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__natAbs_norm_le_pow_of_bounded_b1a71d5dc224

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Formalism.HermitianLatticesTheory Module
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) (V : Type)
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) (hs : h.IsSymm) (hL : IsOrthoLattice h L 2) (s : Finset (Submodule (𝓞 K) V))
    (hreps : Formalism.ThetaLiftIndependence.IsClassReps h L s) (B₁ B₂ : ℝ) (hint : ∀ M ∈ s, IsIntegralLat h M)
    (hshort : ∀ M ∈ s, ∃ x ∈ M, ∃ y ∈ M, x ≠ 0 ∧ y ≠ 0 ∧ h x y = 0 ∧
      ∀ φ : K →+* ℂ, ‖φ (h x x)‖ ≤ B₁ ∧ ‖φ (h y y)‖ ≤ B₂) :
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * B₂) ^ (2 * finrank ℚ K) *
      (B₁ * B₂) ^ (4 * finrank ℚ K) := by
  classical
  have e1 : 0 ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) := by rw [pow_mul]; positivity
  have e2 : 0 ≤ (1 + 2 * B₂) ^ (2 * finrank ℚ K) := by rw [pow_mul]; positivity
  have e3 : 0 ≤ (B₁ * B₂) ^ (4 * finrank ℚ K) := by
    rw [show 4 * finrank ℚ K = 2 * (2 * finrank ℚ K) by ring, pow_mul]; positivity
  rcases s.eq_empty_or_nonempty with rfl | ⟨M₀, hM₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hfr := finrank_orthonormal_plane_eq_two h L hL
  choose! x hx y hy hx0 hy0 hxy hb using hshort
  have hxx : ∀ M ∈ s, h (x M) (x M) ≠ 0 := fun M hM e => hx0 M hM (eq_zero_of_inner_self_eq_zero h hK L hL _ e)
  have hyy : ∀ M ∈ s, h (y M) (y M) ≠ 0 := fun M hM e => hy0 M hM (eq_zero_of_inner_self_eq_zero h hK L hL _ e)
  have hA : ∀ M ∈ s, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = h (x M) (x M) := fun M hM =>
    Submodule.mem_one.1 (hint M hM _ (hx M hM) _ (hx M hM))
  have hBe : ∀ M ∈ s, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = h (y M) (y M) := fun M hM =>
    Submodule.mem_one.1 (hint M hM _ (hy M hM) _ (hy M hM))
  choose! a ha using hA
  choose! b hb' using hBe
  obtain ⟨φ₀⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hB1 : 0 < B₁ := lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero φ₀).2 (hxx M₀ hM₀))) (hb M₀ hM₀ φ₀).1
  have hB2 : 0 < B₂ := lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero φ₀).2 (hyy M₀ hM₀))) (hb M₀ hM₀ φ₀).2
  obtain ⟨f1, c1⟩ := boundedIntegers_finite_card_le K B₁ hB1
  obtain ⟨f2, c2⟩ := boundedIntegers_finite_card_le K B₂ hB2
  have hba : ∀ M ∈ s, ∀ φ : K →+* ℂ, ‖φ ((a M : 𝓞 K) : K)‖ ≤ B₁ := fun M hM φ => by
    have e : ((a M : 𝓞 K) : K) = h (x M) (x M) := ha M hM
    rw [e]; exact (hb M hM φ).1
  have hbb : ∀ M ∈ s, ∀ φ : K →+* ℂ, ‖φ ((b M : 𝓞 K) : K)‖ ≤ B₂ := fun M hM φ => by
    have e : ((b M : 𝓞 K) : K) = h (y M) (y M) := hb' M hM
    rw [e]; exact (hb M hM φ).2
  have hmap : ∀ M ∈ s, (a M, b M) ∈ f1.toFinset ×ˢ f2.toFinset := by
    intro M hM
    rw [Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact ⟨hba M hM, hbb M hM⟩
  have hfib : ∀ q ∈ f1.toFinset ×ˢ f2.toFinset,
      ((s.filter (fun M => (a M, b M) = q)).card : ℝ) ≤ (B₁ * B₂) ^ (4 * finrank ℚ K) := by
    intro q _
    rcases (s.filter (fun M => (a M, b M) = q)).eq_empty_or_nonempty with he | ⟨M₁, hM₁⟩
    · rw [he]; simpa using e3
    obtain ⟨hM₁s, rfl⟩ := Finset.mem_filter.1 hM₁
    have ha0 : a M₁ ≠ 0 := by
      intro e; apply hxx M₁ hM₁s; rw [← ha M₁ hM₁s, e, map_zero]
    have hb0 : b M₁ ≠ 0 := by
      intro e; apply hyy M₁ hM₁s; rw [← hb' M₁ hM₁s, e, map_zero]
    obtain ⟨hfinS, hcardS⟩ := card_submodules_quotient_le K (a M₁ * b M₁) (mul_ne_zero ha0 hb0)
    let Nf : Submodule (𝓞 K) V → Submodule (𝓞 K) (Fin 2 → 𝓞 K) := fun M =>
      M.comap (pairCoords (K := K) ((h (x M) (x M))⁻¹ • x M) ((h (y M) (y M))⁻¹ • y M))
    have hQ : ∀ M ∈ s.filter (fun M => (a M, b M) = (a M₁, b M₁)), scaledFreeModule K (a M₁ * b M₁) ≤ Nf M := by
      intro M hM
      obtain ⟨hMs, hq⟩ := Finset.mem_filter.1 hM
      rw [← (Prod.mk.inj hq).1, ← (Prod.mk.inj hq).2]
      exact scaledFreeModule_le_comap h M (x M) (y M) (hx M hMs) (hy M hMs) (a M) (b M) (ha M hMs) (hb' M hMs) (hxx M hMs)
        (hyy M hMs)
    have hinj : Set.InjOn (fun M => (Nf M).map (scaledFreeModule K (a M₁ * b M₁)).mkQ)
        (s.filter (fun M => (a M, b M) = (a M₁, b M₁)) : Finset (Submodule (𝓞 K) V)) := by
      intro M hM M' hM' hEq
      have hM2 := Finset.mem_coe.1 hM
      have hM2' := Finset.mem_coe.1 hM'
      obtain ⟨hMs, hq⟩ := Finset.mem_filter.1 hM2
      obtain ⟨hMs', hq'⟩ := Finset.mem_filter.1 hM2'
      have hN : Nf M = Nf M' := by
        have h1 := congrArg (Submodule.comap (scaledFreeModule K (a M₁ * b M₁)).mkQ) hEq
        simp only [Submodule.comap_map_mkQ] at h1
        rwa [sup_eq_right.2 (hQ M hM2), sup_eq_right.2 (hQ M' hM2')] at h1
      have hα : h (x M') (x M') = h (x M) (x M) := by
        rw [← ha M hMs, ← ha M' hMs', (Prod.mk.inj hq).1, (Prod.mk.inj hq').1]
      have hβ : h (y M') (y M') = h (y M) (y M) := by
        rw [← hb' M hMs, ← hb' M' hMs', (Prod.mk.inj hq).2, (Prod.mk.inj hq').2]
      have hu := hreps.2 M' (hreps.1 M' hMs')
      have u1 : M' ∈ s ∧ ∃ g ∈ isom h, gmap g M' = M' :=
        ⟨hMs', 1, (isom h).one_mem, by ext v; simp [gmap]⟩
      have u2 : M ∈ s ∧ ∃ g ∈ isom h, gmap g M = M' :=
        ⟨hMs, isometric_of_orthogonal_pairs h hs hfr M M' (hint M hMs) (hint M' hMs') (x M) (y M) (x M') (y M') (hx M hMs)
          (hy M hMs) (hx M' hMs') (hy M' hMs') (hxy M hMs) (hxx M hMs) (hyy M hMs) (hxy M' hMs') hα hβ hN⟩
      exact hu.unique u2 u1
    have := Fintype.ofFinite (Submodule (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K (a M₁ * b M₁)))
    have hc1 : (s.filter (fun M => (a M, b M) = (a M₁, b M₁))).card ≤
        Nat.card (Submodule (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K (a M₁ * b M₁))) := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      exact Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
    have hc2 : ((Algebra.norm ℤ (a M₁ * b M₁)).natAbs : ℝ) ≤ (B₁ * B₂) ^ finrank ℚ K := by
      apply natAbs_norm_le_pow_of_bounded
      intro φ
      have e : (((a M₁ * b M₁ : 𝓞 K)) : K) = ((a M₁ : 𝓞 K) : K) * ((b M₁ : 𝓞 K) : K) := map_mul _ _ _
      rw [e, map_mul, norm_mul]
      exact mul_le_mul (hba M₁ hM₁s φ) (hbb M₁ hM₁s φ) (norm_nonneg _) hB1.le
    calc ((s.filter (fun M => (a M, b M) = (a M₁, b M₁))).card : ℝ)
        ≤ (((((Algebra.norm ℤ (a M₁ * b M₁)).natAbs ^ 2) ^ 2 : ℕ)) : ℝ) := by exact_mod_cast hc1.trans hcardS
      _ = (((Algebra.norm ℤ (a M₁ * b M₁)).natAbs : ℝ) ^ 2) ^ 2 := by push_cast; rfl
      _ ≤ (((B₁ * B₂) ^ finrank ℚ K) ^ 2) ^ 2 := by gcongr
      _ = (B₁ * B₂) ^ (4 * finrank ℚ K) := by
          rw [← pow_mul, ← pow_mul]; congr 1; ring
  have hsum : (s.card : ℝ) = ∑ q ∈ f1.toFinset ×ˢ f2.toFinset,
      ((s.filter (fun M => (a M, b M) = q)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun M => (a M, b M)) (t := f1.toFinset ×ˢ f2.toFinset)
      (fun M hM => hmap M hM)]
    push_cast; rfl
  rw [hsum]
  calc ∑ q ∈ f1.toFinset ×ˢ f2.toFinset, ((s.filter (fun M => (a M, b M) = q)).card : ℝ)
      ≤ ∑ _q ∈ f1.toFinset ×ˢ f2.toFinset, (B₁ * B₂) ^ (4 * finrank ℚ K) := Finset.sum_le_sum hfib
    _ = ((f1.toFinset.card : ℝ) * (f2.toFinset.card : ℝ)) * (B₁ * B₂) ^ (4 * finrank ℚ K) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]; push_cast; rfl
    _ ≤ ((1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * B₂) ^ (2 * finrank ℚ K)) *
          (B₁ * B₂) ^ (4 * finrank ℚ K) := by
        rw [← Set.ncard_eq_toFinset_card _ f1, ← Set.ncard_eq_toFinset_card _ f2]
        exact mul_le_mul_of_nonneg_right (mul_le_mul c1 c2 (Nat.cast_nonneg _) e1) e3
end Formalism.MainNotions.BridgeLemma₂
