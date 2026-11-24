-- Prove2me | solution 1 for QCQPTightness.Exact.separation_step
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T13:11:20.355669+00:00
-- url     : https://prove2.me/submissions/9135f3d7-78dd-4c35-9a8c-e77bc912af22

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP
import Definitions.Def_QCQPTightness_Exact_Faces
import Definitions.Def_QCQPTightness_Exact_Proj

open Matrix QCQPTightness.Exact

namespace SepStepAux

/-- An affine image of a set cut out of an affine subspace by finitely many linear inequalities is
closed. Induction on the number of inequalities. -/
theorem closed_image {E G : Type*} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] (T : E →ᵃ[ℝ] G) :
    ∀ (n : ℕ) (A : AffineSubspace ℝ E) (α : Fin n → E →ₗ[ℝ] ℝ) (β : Fin n → ℝ),
      IsClosed (T '' {x | x ∈ A ∧ ∀ j, α j x ≤ β j}) := by
  intro n
  induction n with
  | zero =>
    intro A α β
    have h : {x | x ∈ A ∧ ∀ j : Fin 0, α j x ≤ β j} = (A : Set E) := by
      ext x
      simp
    rw [h, ← AffineSubspace.coe_map]
    exact AffineSubspace.closed_of_finiteDimensional _
  | succ n ih =>
    intro A α β
    set P' : Set E := {x | x ∈ A ∧ ∀ j : Fin n, α j.castSucc x ≤ β j.castSucc} with hP'
    have hcl' : IsClosed (T '' P') := ih A (fun j => α j.castSucc) (fun j => β j.castSucc)
    set a := α (Fin.last n) with ha
    set b := β (Fin.last n) with hb
    have hP : {x | x ∈ A ∧ ∀ j : Fin (n + 1), α j x ≤ β j} = {x | x ∈ P' ∧ a x ≤ b} := by
      ext x
      simp only [Set.mem_ofPred_eq, hP']
      constructor
      · rintro ⟨hA, h⟩
        exact ⟨⟨hA, fun j => h _⟩, h _⟩
      · rintro ⟨⟨hA, h⟩, hl⟩
        exact ⟨hA, fun j => Fin.lastCases hl (fun i => h i) j⟩
    rw [hP]
    refine isClosed_of_closure_subset fun y hy => ?_
    have hy' : y ∈ T '' P' := by
      rw [← hcl'.closure_eq]
      exact closure_mono (Set.image_mono fun x hx => hx.1) hy
    obtain ⟨x', hx', rfl⟩ := hy'
    by_cases hax : a x' ≤ b
    · exact ⟨x', ⟨hx', hax⟩, rfl⟩
    have hax' : b < a x' := not_le.1 hax
    -- every admissible point is joined to x' by a segment crossing the hyperplane a = b
    have hz : ∀ x, x ∈ P' → a x ≤ b →
        ∃ z, z ∈ P' ∧ a z = b ∧ dist (T x') (T z) ≤ dist (T x') (T x) := by
      intro x hx hxb
      have hden : 0 < a x' - a x := by linarith
      set t : ℝ := (a x' - b) / (a x' - a x) with ht
      have ht0 : 0 ≤ t := div_nonneg (by linarith) hden.le
      have ht1 : t ≤ 1 := (div_le_one hden).2 (by linarith)
      have htd : t * (a x' - a x) = a x' - b := div_mul_cancel₀ _ hden.ne'
      refine ⟨AffineMap.lineMap x' x t, ⟨AffineMap.lineMap_mem t hx'.1 hx.1, fun j => ?_⟩, ?_, ?_⟩
      · have h1 := hx'.2 j
        have h2 := hx.2 j
        have e : α j.castSucc (AffineMap.lineMap x' x t) =
            t * (α j.castSucc x - α j.castSucc x') + α j.castSucc x' := by
          simp [AffineMap.lineMap_apply_module']
        rw [e]
        nlinarith [mul_nonneg ht0 (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 h1)]
      · have e : a (AffineMap.lineMap x' x t) = t * (a x - a x') + a x' := by
          simp [AffineMap.lineMap_apply_module']
        rw [e]
        linarith
      · rw [AffineMap.apply_lineMap, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht0]
        exact mul_le_of_le_one_left dist_nonneg ht1
    obtain ⟨w1, ⟨x1, ⟨hx1, hx1b⟩, -⟩, -⟩ := Metric.mem_closure_iff.1 hy 1 one_pos
    obtain ⟨z0, hz0, hz0b, -⟩ := hz x1 hx1 hx1b
    set S : Set E := {x | x ∈ A ⊓ AffineSubspace.mk' z0 (LinearMap.ker a) ∧
      ∀ j : Fin n, α j.castSucc x ≤ β j.castSucc} with hS
    have hclS : IsClosed (T '' S) :=
      ih (A ⊓ AffineSubspace.mk' z0 (LinearMap.ker a)) (fun j => α j.castSucc)
        (fun j => β j.castSucc)
    have hmem : T x' ∈ closure (T '' S) := by
      refine Metric.mem_closure_iff.2 fun ε hε => ?_
      obtain ⟨w, ⟨x, ⟨hx, hxb⟩, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 hy ε hε
      obtain ⟨z, hzP, hzb, hzd⟩ := hz x hx hxb
      refine ⟨T z, ⟨z, ⟨⟨hzP.1, ?_⟩, hzP.2⟩, rfl⟩, lt_of_le_of_lt hzd hd⟩
      change z -ᵥ z0 ∈ LinearMap.ker a
      rw [LinearMap.mem_ker, vsub_eq_sub, map_sub, hzb, hz0b, sub_self]
    rw [hclS.closure_eq] at hmem
    obtain ⟨z, ⟨⟨hzA, hzk⟩, hzj⟩, hzT⟩ := hmem
    change z -ᵥ z0 ∈ LinearMap.ker a at hzk
    rw [LinearMap.mem_ker, vsub_eq_sub, map_sub, hz0b, sub_eq_zero] at hzk
    exact ⟨z, ⟨⟨hzA, hzj⟩, hzk.le⟩, hzT⟩

/-- A nonempty convex extreme subset of a set contains every point of that set lying in its
affine span. -/
theorem face_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Γ F : Set E} (hne : F.Nonempty) (hconv : Convex ℝ F) (hext : IsExtreme ℝ Γ F) {y : E}
    (hyΓ : y ∈ Γ) (hyS : y ∈ affineSpan ℝ F) : y ∈ F := by
  obtain ⟨x0, hx0⟩ := hne.intrinsicInterior hconv
  obtain ⟨x, hxint, rfl⟩ := mem_intrinsicInterior.1 hx0
  have hxF : (x : E) ∈ F := intrinsicInterior_subset hx0
  set g : ℝ → affineSpan ℝ F :=
    fun t => ⟨AffineMap.lineMap (x : E) y (-t), AffineMap.lineMap_mem _ x.2 hyS⟩ with hg
  have hgc : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    simp only [AffineMap.lineMap_apply_module']
    fun_prop
  have hg0 : g 0 = x := by
    apply Subtype.ext
    simp [hg]
  have hopen : IsOpen (g ⁻¹' interior ((↑) ⁻¹' F : Set (affineSpan ℝ F))) :=
    isOpen_interior.preimage hgc
  have h0 : (0 : ℝ) ∈ g ⁻¹' interior ((↑) ⁻¹' F : Set (affineSpan ℝ F)) := by
    rw [Set.mem_preimage, hg0]
    exact hxint
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  set t : ℝ := δ / 2 with ht
  have htpos : 0 < t := by positivity
  have htb : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    linarith
  have hgt : g t ∈ ((↑) ⁻¹' F : Set (affineSpan ℝ F)) := interior_subset (hball htb)
  have hzF : AffineMap.lineMap (x : E) y (-t) ∈ F := hgt
  have hseg : (x : E) ∈ openSegment ℝ y (AffineMap.lineMap (x : E) y (-t)) := by
    refine ⟨t / (1 + t), 1 / (1 + t), by positivity, by positivity,
      by rw [← add_div, add_comm t 1, div_self (by positivity)], ?_⟩
    have e : (t / (1 + t)) • y + (1 / (1 + t)) • AffineMap.lineMap (x : E) y (-t) =
        (t / (1 + t) - 1 / (1 + t) * t) • y + (1 / (1 + t) * (1 + t)) • (x : E) := by
      rw [AffineMap.lineMap_apply_module']
      module
    rw [e, show t / (1 + t) - 1 / (1 + t) * t = 0 by ring,
      one_div_mul_cancel (by positivity : (1 + t) ≠ 0), zero_smul, one_smul, zero_add]
  exact hext.left_mem_of_mem_openSegment hyΓ (hext.subset hzF) hxF hseg

end SepStepAux

theorem solution {N m : ℕ} (P : QCQP N m) (h3 : P.Assumption3)
    (F : Set (Fin m → ℝ)) (hF : P.IsSemidefiniteFace F)
    (h0 : (0 : EuclideanSpace ℝ (Fin N)) ∉ projB P F) :
    ∃ v ∈ P.V F, v ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ γ ∈ F, P.bγ γ ⬝ᵥ v ≤ -ε := by
  obtain ⟨⟨hne, hconv, hext⟩, -⟩ := hF
  obtain ⟨p, a, β, hΓ⟩ := h3
  let bL : (Fin m → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
    { toFun := fun γ => ∑ i, γ i • P.b i
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }
  let Λ : (Fin m → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin N) :=
    (VE P F).starProjection.toLinearMap ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.toLinearMap ∘ₗ bL
  have hb : ∀ γ, P.bγ γ = bL γ + P.bγ 0 := by
    intro γ
    simp [QCQP.bγ, bL, add_comm]
  let T : (Fin m → ℝ) →ᵃ[ℝ] EuclideanSpace ℝ (Fin N) :=
    AffineMap.mk' (fun γ => (VE P F).starProjection (WithLp.toLp 2 (P.bγ γ))) Λ 0 (by
      intro γ
      show (VE P F).starProjection (WithLp.toLp 2 (P.bγ γ)) =
        (VE P F).starProjection (WithLp.toLp 2 (bL (γ - 0))) +
          (VE P F).starProjection (WithLp.toLp 2 (P.bγ 0))
      rw [sub_zero, ← map_add, ← WithLp.toLp_add, ← hb])
  let α : Fin p → (Fin m → ℝ) →ₗ[ℝ] ℝ := fun j =>
    { toFun := fun x => a j ⬝ᵥ x
      map_add' := fun x y => dotProduct_add _ _ _
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hFeq : F = {x | x ∈ affineSpan ℝ F ∧ ∀ j, α j x ≤ β j} := by
    ext x
    constructor
    · intro hx
      have hxΓ := hext.subset hx
      rw [hΓ] at hxΓ
      exact ⟨subset_affineSpan _ _ hx, hxΓ⟩
    · rintro ⟨h1, h2⟩
      refine SepStepAux.face_mem hne hconv hext ?_ h1
      rw [hΓ]
      exact h2
  have hcl : IsClosed (T '' {x | x ∈ affineSpan ℝ F ∧ ∀ j, α j x ≤ β j}) :=
    SepStepAux.closed_image T p _ α β
  have hB : projB P F = T '' {x | x ∈ affineSpan ℝ F ∧ ∀ j, α j x ≤ β j} :=
    congrArg (fun S => (fun γ => (VE P F).starProjection (WithLp.toLp 2 (P.bγ γ))) '' S) hFeq
  have hclB : IsClosed (projB P F) := hB ▸ hcl
  have hconvB : Convex ℝ (projB P F) := hconv.affine_image T
  obtain ⟨φ, u, hu0, hub⟩ := geometric_hahn_banach_point_closed hconvB hclB h0
  have hu : 0 < u := by simpa using hu0
  set w := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm φ with hw
  have hmem : (VE P F).starProjection w ∈
      (P.V F).map (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.toLinearMap :=
    (VE P F).starProjection_apply_mem w
  obtain ⟨v0, hv0, hv0eq⟩ := Submodule.mem_map.1 hmem
  have hv0eq' : WithLp.toLp 2 v0 = (VE P F).starProjection w := hv0eq
  have key : ∀ γ ∈ F, u < P.bγ γ ⬝ᵥ v0 := by
    intro γ hγ
    have h1 : P.bγ γ ⬝ᵥ v0 = φ ((VE P F).starProjection (WithLp.toLp 2 (P.bγ γ))) := by
      rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ), ← hw,
        ← Submodule.inner_starProjection_left_eq_right, ← hv0eq', EuclideanSpace.inner_toLp_toLp,
        star_trivial]
    rw [h1]
    exact hub _ ⟨γ, hγ, rfl⟩
  refine ⟨-v0, (P.V F).neg_mem hv0, ?_, u, hu, fun γ hγ => ?_⟩
  · intro h
    obtain ⟨γ0, hγ0⟩ := hne
    have hk := key γ0 hγ0
    rw [neg_eq_zero.1 h, dotProduct_zero] at hk
    linarith
  · rw [dotProduct_neg]
    linarith [key γ hγ]
