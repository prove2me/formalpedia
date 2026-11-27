-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_proof_c3395fbafb47
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:56:16.986889+00:00
-- url     : https://prove2.me/submissions/1080d730-558a-451a-8e7b-0e6946f0e9e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LineDegreeBundleStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLineDegreeBundle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_index_span_smul_210a9f4dbdea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_cardQuot_span_singleton_4f89c053a314
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_sum_log_norm_e180af1d2243
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_quad_smul_a3693f548c14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_quad_pos_4b2ebda8dd85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_satLine_map_eq_a4ce591a1c83


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder nonZeroDivisors
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
namespace LineDegreeBundle
theorem _root_.solution : LineDegreeBundle.Statement := by
  intro K _ _ n F hF K' _ _ _ E φ hE v hv
  classical
  set M : Submodule (𝓞 K') E.carrier := (satLine v).comap φ.toLinearMap with hM
  set v' : Fin n → K' := fun j ↦ (v j : K') with hv'
  let ψ : E.carrier →ₗ[𝓞 K'] (Fin n → K') := intoField K' n ∘ₗ φ.toLinearMap
  have hψ_apply : ∀ x j, ψ x j = (φ x j : K') := fun _ _ ↦ rfl
  have hψ : Function.Injective ψ := by
    intro x y h
    apply φ.injective
    funext j
    exact RingOfIntegers.ext (congrFun h j)
  have : Module.IsTorsionFree (𝓞 K') E.carrier := by
    refine Module.isTorsionFree_iff_smul_eq_zero.mpr fun r x h ↦ ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    refine Or.inr (φ.injective ?_)
    funext j
    have h' := congrFun (congrArg φ h) j
    rw [map_smul, map_zero, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h'
    rw [map_zero, Pi.zero_apply]
    exact (mul_eq_zero.mp h').resolve_left hr
  have : Module.IsTorsionFree (𝓞 K') M :=
    Function.Injective.moduleIsTorsionFree M.subtype Subtype.val_injective (fun _ _ ↦ rfl)
  have hmem : ∀ x : E.carrier, x ∈ M ↔ ∃ c : K', ∀ j, (φ x j : K') = c * v j := fun x ↦ Iff.rfl
  have hmM : φ.symm v ∈ M := (hmem _).2 ⟨1, fun j ↦ by simp⟩
  set m : M := ⟨φ.symm v, hmM⟩ with hm
  have hψm : ψ m = v' := by funext j; simp [hψ_apply, m, hv']
  have hm0 : m ≠ 0 := by
    intro h
    apply hv
    have h' : ψ m = ψ 0 := congrArg (fun y : M ↦ ψ (y : E.carrier)) h
    rw [hψm, map_zero] at h'
    funext j
    exact RingOfIntegers.ext (by simpa [hv'] using congrFun h' j)

  have hrel : ∀ x : M, ∃ (c : K') (a b : 𝓞 K'), b ≠ 0 ∧ ψ x = c • v' ∧ c * (b : K') = a ∧
      b • x = a • m := by
    intro x
    obtain ⟨c, hc⟩ := (hmem x).1 x.2
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (𝓞 K')⁰ c
    dsimp only at hab
    have h1 : ψ x = c • v' := by funext j; rw [hψ_apply, hc j]; rfl
    refine ⟨c, a, b, nonZeroDivisors.coe_ne_zero b, h1, hab, ?_⟩
    apply Subtype.ext
    apply hψ
    rw [Submodule.coe_smul, Submodule.coe_smul, map_smul, map_smul, h1, hψm]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Algebra.smul_def, Algebra.smul_def, ← hab]
    ring

  have hrank : E.rank M = 1 := by
    unfold HermitianBundle.rank
    apply le_antisymm
    · by_contra h
      push Not at h
      obtain ⟨g, hg⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K') (M := M) (n := 2) (by omega)
      have hg2 : LinearIndependent (𝓞 K') ![g 0, g 1] := by
        convert hg using 1
        funext i
        fin_cases i <;> rfl
      obtain ⟨-, a₁, b₁, hb₁, -, -, h₁⟩ := hrel (g 0)
      obtain ⟨-, a₂, b₂, hb₂, -, -, h₂⟩ := hrel (g 1)
      have h0 := LinearIndependent.pair_iff.mp hg2 (a₂ * b₁) (-(a₁ * b₂)) (by
        rw [mul_smul, h₁, neg_smul, mul_smul, h₂, smul_smul, smul_smul, mul_comm a₂ a₁, add_neg_cancel])
      have ha₁ : a₁ = 0 := (mul_eq_zero.mp (neg_eq_zero.mp h0.2)).resolve_right hb₂
      rw [ha₁, zero_smul] at h₁
      exact hg.ne_zero 0 ((smul_eq_zero.mp h₁).resolve_left hb₁)
    · have := (linearIndependent_unique_iff (v := fun _ : Fin 1 ↦ m) (R := 𝓞 K')).mpr hm0
      simpa using this.fintype_card_le_finrank

  have hIm : (Submodule.span (𝓞 K') {m}).toAddSubgroup.index ≠ 0 := by
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hv
    have hd : v j₀ ≠ 0 := hj₀
    have hfin : Finite (𝓞 K' ⧸ Ideal.span {v j₀}) := by
      apply Nat.finite_of_card_ne_zero
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
      exact Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hd)
    let g : M →ₗ[𝓞 K'] 𝓞 K' ⧸ Ideal.span {v j₀} :=
      (Ideal.span {v j₀}).mkQ ∘ₗ LinearMap.proj j₀ ∘ₗ φ.toLinearMap ∘ₗ M.subtype
    have hker : (LinearMap.ker g).toAddSubgroup ≤ (Submodule.span (𝓞 K') {m}).toAddSubgroup := by
      intro x hx
      have hx' : g x = 0 := hx
      have h1 : φ x j₀ ∈ Ideal.span {v j₀} := (Submodule.Quotient.mk_eq_zero _).mp hx'
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h1
      obtain ⟨c, hc⟩ := (hmem x).1 x.2
      have hct : c = t := by
        have h2 := hc j₀
        rw [← ht] at h2
        push_cast at h2
        exact (mul_right_cancel₀ (by exact_mod_cast hd) h2).symm
      change x ∈ Submodule.span (𝓞 K') {m}
      rw [Submodule.mem_span_singleton]
      refine ⟨t, Subtype.ext (hψ ?_)⟩
      rw [Submodule.coe_smul, map_smul, hψm]
      funext j
      rw [Pi.smul_apply, hψ_apply, hc j, hct, Algebra.smul_def]
    have h2 : (LinearMap.ker g).toAddSubgroup.index ≠ 0 := by
      have : (LinearMap.ker g).toAddSubgroup = (g.toAddMonoidHom).ker := AddSubgroup.ext fun _ ↦ Iff.rfl
      rw [this, AddSubgroup.index_ker]
      exact Nat.card_pos.ne'
    exact ne_zero_of_dvd_ne_zero h2 (AddSubgroup.index_dvd_of_le hker)

  let Q : (K' →+* ℂ) → ℂ := fun σ' ↦
    star (embVec σ' v') ⬝ᵥ (F.metric (σ'.comp (algebraMap K K')) *ᵥ embVec σ' v')
  have hQ : ∀ σ' : K' →+* ℂ, ‖Q σ'‖ = (Q σ').re ∧ 0 < (Q σ').re := by
    intro σ'
    apply LineDegreeBundle.quad_pos (F.posDef _)
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hv
    intro h
    have h3 := congrFun h j₀
    simp only [embVec, Pi.zero_apply, map_eq_zero_iff _ σ'.injective, hv'] at h3
    exact hj₀ (RingOfIntegers.ext (by simpa using h3))

  have hdeg : ∀ (r : ℕ) (f : Fin r → M), r = 1 → LinearIndependent (𝓞 K') f →
      HermitianBundle.degreeWith E M f =
        Real.log ((Submodule.span (𝓞 K') {m}).toAddSubgroup.index : ℝ) -
          1 / 2 * ∑ σ' : K' →+* ℂ, Real.log (Q σ').re := by
    rintro r f rfl hf
    have hx : f 0 ≠ 0 := hf.ne_zero 0
    obtain ⟨c, a, b, hb, hxc, hab, hba⟩ := hrel (f 0)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hxc
      exact hx (Subtype.ext (hψ (by rw [hxc, Submodule.coe_zero, map_zero])))
    have hxj : ∀ j, (φ (f 0 : E.carrier) j : K') = c * v' j := fun j ↦ congrFun hxc j

    have hidx : ((Submodule.span (𝓞 K') {f 0}).toAddSubgroup.index : ℝ) =
        (Submodule.span (𝓞 K') {m}).toAddSubgroup.index * |(Algebra.norm ℚ c : ℝ)| := by
      have e1 := LineDegreeBundle.index_span_smul hx b
      have e2 := LineDegreeBundle.index_span_smul hm0 a
      rw [hba, e2] at e1
      have e3 : ((Submodule.cardQuot (Ideal.span {a} : Ideal (𝓞 K')) *
          (Submodule.span (𝓞 K') {m}).toAddSubgroup.index : ℕ) : ℝ) =
          ((Submodule.cardQuot (Ideal.span {b} : Ideal (𝓞 K')) *
          (Submodule.span (𝓞 K') {f 0}).toAddSubgroup.index : ℕ) : ℝ) := by rw [e1]
      push_cast at e3
      rw [LineDegreeBundle.cardQuot_span_singleton, LineDegreeBundle.cardQuot_span_singleton, ← hab,
        map_mul, Rat.cast_mul, abs_mul] at e3
      have hbn : |(Algebra.norm ℚ (b : K') : ℝ)| ≠ 0 := by
        rw [abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]
        exact_mod_cast hb
      apply mul_right_cancel₀ hbn
      linear_combination -e3

    have hgram : ∀ σ' : K' →+* ℂ,
        Real.log ‖HermitianBundle.gramDet E σ' (fun i ↦ (f i : E.carrier))‖ =
          2 * Real.log ‖σ' c‖ + Real.log (Q σ').re := by
      intro σ'
      have hv1 : (fun j ↦ σ' (φ (f 0 : E.carrier) j : K')) = σ' c • embVec σ' v' := by
        funext j
        rw [hxj j, map_mul]
        rfl
      have : HermitianBundle.gramDet E σ' (fun i ↦ (f i : E.carrier)) = (star (σ' c) * σ' c) * Q σ' := by
        unfold HermitianBundle.gramDet
        rw [Matrix.det_unique, Matrix.of_apply]
        rw [show (default : Fin 1) = 0 from rfl, hE σ', hv1, LineDegreeBundle.quad_smul]
      rw [this, norm_mul, norm_mul, norm_star, (hQ σ').1, Real.log_mul, Real.log_mul, ← two_mul]
      · exact norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hc0)
      · exact norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hc0)
      · exact mul_ne_zero (norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hc0))
          (norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hc0))
      · exact (hQ σ').2.ne'
    unfold HermitianBundle.degreeWith
    rw [Set.range_unique, show (default : Fin 1) = 0 from rfl, ← Submodule.cardQuot_apply]
    change Real.log ((Submodule.span (𝓞 K') {f 0}).toAddSubgroup.index : ℝ) - _ = _
    simp only [hgram]
    rw [hidx, Finset.sum_add_distrib, ← Finset.mul_sum, LineDegreeBundle.sum_log_norm hc0,
      Real.log_mul (by exact_mod_cast hIm) (by simpa [abs_ne_zero, Algebra.norm_ne_zero_iff] using hc0)]
    ring

  have hinj : Function.Injective (ψ ∘ₗ M.subtype) := hψ.comp Subtype.val_injective
  have hA : (satLine v).map (intoField K' n) = (⊤ : Submodule (𝓞 K') M).map (ψ ∘ₗ M.subtype) := by
    rw [Submodule.map_comp, Submodule.map_subtype_top, hM, Submodule.map_comp,
      Submodule.map_comap_eq_of_surjective φ.surjective]
  have hB : Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v') =
      (Submodule.span (𝓞 K') {m}).map (ψ ∘ₗ M.subtype) := by
    rw [Submodule.map_span, Set.image_singleton, Set.range_const]
    simp [hψm]
  have hgen : genIndex ((satLine v).map (intoField K' n)).toAddSubgroup
      (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v')).toAddSubgroup =
      (Submodule.span (𝓞 K') {m}).toAddSubgroup.index := by
    unfold genIndex
    rw [hA, hB, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
      AddSubgroup.relIndex_map_map_of_injective _ _ hinj, Submodule.top_toAddSubgroup,
      AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_eq_one.mpr le_top]
    simp
  unfold HermitianBundle.normDegree HermitianBundle.degree HermLattice.lineDegree normalise subDegree
  rw [hdeg _ _ hrank (HermitianBundle.exists_linearIndependent_rank E M).choose_spec, hF,
    ← satLine_map_eq v, hgen]
  congr 3
  refine Finset.sum_congr rfl fun σ' _ ↦ ?_
  rw [Matrix.det_unique]
  rfl
end LineDegreeBundle
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
