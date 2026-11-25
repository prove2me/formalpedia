-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_CoordinateDegree_proof_c089f0b8db1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:33:35.567409+00:00
-- url     : https://prove2.me/submissions/ccbdbec7-d15c-458e-844a-042a11c7968c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_SpanEqTopSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_genIndex_eq_div_of_le_aa8fc90600a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_exists_smul_mem_of_span_eq_top_707bad7a4bf7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_gramAt_smul_193511ca268a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_arithDegree_1ab30fd3c0e4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.CoordinateDegree
theorem _root_.solution : S6.CoordinateDegree.Statement := by
  intro K _ _ E n H ψ hψ hspan hmet G ι _ _ u hu hG
  have hu' : LinearIndependent (𝓞 K) u := (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr hu
  obtain ⟨t, ht0, htu⟩ : ∃ t : 𝓞 K, t ≠ 0 ∧ ∀ j, t • u j ∈ LinearMap.range ψ := by
    choose a ha hau using fun j => exists_smul_mem_of_span_eq_top (LinearMap.range ψ) hspan (u j)
    refine ⟨∏ j, a j, Finset.prod_ne_zero_iff.mpr fun j _ => ha j, fun j => ?_⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ j)
    rw [hc, mul_comm, mul_smul]
    exact (LinearMap.range ψ).smul_mem c (hau j)
  have htW : ∀ j, t • u j ∈ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K) := fun j =>
    (Submodule.span K (Set.range u)).smul_of_tower_mem t (Submodule.subset_span ⟨j, rfl⟩)
  have hmemG : ∀ j, t • u j ∈ G.map ψ := by
    intro j
    rw [hG]
    exact ⟨htu j, htW j⟩
  choose f0 hf0G hf0 using fun j => Submodule.mem_map.mp (hmemG j)
  let f : ι → G := fun j => ⟨f0 j, hf0G j⟩
  have htK : algebraMap (𝓞 K) K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ht0
  have htu_li : LinearIndependent (𝓞 K) (fun j => t • u j) := by
    refine (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr ?_
    have h := hu.units_smul (fun _ : ι => Units.mk0 _ htK)
    have he : (fun j => t • u j) = (fun _ : ι => Units.mk0 _ htK) • u := by
      funext j
      simp only [Pi.smul_apply', Units.smul_def, Units.val_mk0, algebraMap_smul]
    rw [he]
    exact h
  have hf_li : LinearIndependent (𝓞 K) f := by
    refine LinearIndependent.of_comp (ψ ∘ₗ G.subtype) ?_
    have : (ψ ∘ₗ G.subtype) ∘ f = fun j => t • u j := funext hf0
    rw [this]
    exact htu_li

  have hcard : Fintype.card ι = Module.finrank (𝓞 K) G := by
    refine le_antisymm hf_li.fintype_card_le_finrank ?_
    obtain ⟨g, hg⟩ := HermitianBundle.exists_linearIndependent_rank E G
    have hgW : ∀ i, ψ (g i) ∈ Submodule.span K (Set.range u) := by
      intro i
      have hi : ψ (g i) ∈ G.map ψ := Submodule.mem_map_of_mem (g i).2
      rw [hG] at hi
      exact hi.2
    let v : Fin (HermitianBundle.rank E G) → Submodule.span K (Set.range u) :=
      fun i => ⟨ψ (g i), hgW i⟩
    have hv : LinearIndependent K v := by
      refine LinearIndependent.of_comp (Submodule.span K (Set.range u)).subtype ?_
      refine (LinearIndependent.iff_fractionRing (𝓞 K) K).mp ?_
      exact hg.map' (ψ ∘ₗ G.subtype) (LinearMap.ker_eq_bot.mpr (hψ.comp G.injective_subtype))
    have := hv.fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_span_eq_card hu] at this
    exact this

  have hCA' : Submodule.span (𝓞 K) (Set.range fun j => t • u j) ≤
      LinearMap.range ψ ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => ⟨htu j, htW j⟩)
  have hCB' : Submodule.span (𝓞 K) (Set.range fun j => t • u j) ≤
      Submodule.span (𝓞 K) (Set.range u) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j =>
      Submodule.smul_mem _ t (Submodule.subset_span ⟨j, rfl⟩))
  have hCA : (Submodule.span (𝓞 K) (Set.range fun j => t • u j)).toAddSubgroup ≤
      (LinearMap.range ψ ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup :=
    fun _ hx => hCA' hx
  have hCB : (Submodule.span (𝓞 K) (Set.range fun j => t • u j)).toAddSubgroup ≤
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup :=
    fun _ hx => hCB' hx
  have h1 : (Submodule.span (𝓞 K) (Set.range fun j => t • u j)).toAddSubgroup.relIndex
      (LinearMap.range ψ ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup =
      Nat.card (G ⧸ Submodule.span (𝓞 K) (Set.range f)) := by
    have hS : (Submodule.span (𝓞 K) (Set.range fun j => (f j : E.carrier))).map ψ =
        Submodule.span (𝓞 K) (Set.range fun j => t • u j) := by
      rw [Submodule.map_span, ← Set.range_comp]
      exact congrArg _ (congrArg Set.range (funext hf0))
    rw [← hG, ← hS, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ hψ]
    have hsp : Submodule.span (𝓞 K) (Set.range f) =
        (Submodule.span (𝓞 K) (Set.range fun j => (f j : E.carrier))).comap G.subtype := by
      rw [← Submodule.comap_map_eq_of_injective G.injective_subtype
        (Submodule.span (𝓞 K) (Set.range f)), Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hsp]
    rfl
  have h2 : (Submodule.span (𝓞 K) (Set.range fun j => t • u j)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup =
      (Algebra.norm ℤ t).natAbs ^ Fintype.card ι := by
    have hΦ : Function.Injective (Fintype.linearCombination (𝓞 K) u) :=
      hu'.fintypeLinearCombination_injective
    let Dm : Matrix ι ι (𝓞 K) := Matrix.diagonal fun _ => t
    have hDet : Dm.det = t ^ Fintype.card ι := by
      simp [Dm, Matrix.det_diagonal]
    have hcomp : Fintype.linearCombination (𝓞 K) u ∘ₗ Dm.mulVecLin =
        Fintype.linearCombination (𝓞 K) (fun j => t • u j) := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Fintype.linearCombination_apply, Dm,
        Matrix.mulVec_diagonal]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, mul_smul, smul_comm]
    rw [← Fintype.range_linearCombination, ← Fintype.range_linearCombination, ← hcomp,
      LinearMap.range_comp, LinearMap.range_eq_map (Fintype.linearCombination (𝓞 K) u),
      Submodule.map_toAddSubgroup,
      Submodule.map_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ hΦ,
      Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]
    change Nat.card ((ι → 𝓞 K) ⧸ LinearMap.range Dm.mulVecLin) = _
    rw [card_quotient_mulVecLin Dm (by rw [hDet]; exact pow_ne_zero _ ht0), hDet, map_pow,
      Int.natAbs_pow]
  have hM0 : (Algebra.norm ℤ t).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ht0)
  have hidx : genIndex
      (LinearMap.range ψ ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup =
      (Nat.card (G ⧸ Submodule.span (𝓞 K) (Set.range f)) : ℝ) /
        ((Algebra.norm ℤ t).natAbs : ℝ) ^ Fintype.card ι := by
    rw [genIndex_eq_div_of_le hCA hCB (by rw [h2]; exact pow_ne_zero _ hM0), h1, h2]
    push_cast
    rfl

  have hgram : ∀ σ : K →+* ℂ,
      GroundTheory.Heights₂.Heights.gramDet (E.metric.comap G.subtype G.injective_subtype) σ f =
        (‖σ (algebraMap (𝓞 K) K t)‖ ^ 2) ^ Fintype.card ι * (gramAt (H σ) σ u).det.re := by
    intro σ
    have hM : (gram ℂ fun i => fibreVec (E.metric.comap G.subtype G.injective_subtype) σ (f i)) =
        ((‖σ (algebraMap (𝓞 K) K t)‖ ^ 2 : ℝ) : ℂ) • gramAt (H σ) σ u := by
      rw [← gramAt_smul]
      ext i j
      change (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f i : E.carrier))
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f j : E.carrier)) = _
      rw [hmet]
      simp only [gramAt, f, hf0, algebraMap_smul]
    simp only [GroundTheory.Heights₂.Heights.gramDet]
    rw [hM, Matrix.det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hpos : ∀ σ : K →+* ℂ, 0 < ‖σ (algebraMap (𝓞 K) K t)‖ := fun σ =>
    norm_pos_iff.mpr ((map_ne_zero σ).mpr htK)
  have hD : ∀ σ : K →+* ℂ, 0 < (gramAt (H σ) σ u).det.re := by
    intro σ
    have h := gramDet_pos (E.metric.comap G.subtype G.injective_subtype) σ hf_li
    rw [hgram σ] at h
    exact pos_of_mul_pos_right h (by positivity)
  have hN : (0 : ℝ) < Nat.card (G ⧸ Submodule.span (𝓞 K) (Set.range f)) := by
    have := finite_quotient_span hf_li hcard
    exact_mod_cast Nat.card_pos
  have hMpos : (0 : ℝ) < ((Algebra.norm ℤ t).natAbs : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM0
  have hsum : ∑ σ : K →+* ℂ, Real.log ((‖σ (algebraMap (𝓞 K) K t)‖ ^ 2) ^ Fintype.card ι *
      (gramAt (H σ) σ u).det.re) = 2 * Fintype.card ι * Real.log ((Algebra.norm ℤ t).natAbs : ℝ) +
      ∑ σ : K →+* ℂ, Real.log (gramAt (H σ) σ u).det.re := by
    rw [← sum_log_norm_embedding t ht0, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Real.log_mul (pow_pos (pow_pos (hpos σ) 2) _).ne' (hD σ).ne', Real.log_pow, Real.log_pow,
      show algebraMap (𝓞 K) K t = (t : K) from rfl]
    push_cast
    ring

  rw [HermitianBundle.degree_eq_arithDegree, arithDegree_eq _ hf_li hcard, GroundTheory.Heights₂.Heights.degreeWith,
    subDegree, hidx]
  simp only [hgram]
  rw [hsum, Real.log_div hN.ne' (pow_pos hMpos _).ne', Real.log_pow]
  ring
end S6.CoordinateDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
