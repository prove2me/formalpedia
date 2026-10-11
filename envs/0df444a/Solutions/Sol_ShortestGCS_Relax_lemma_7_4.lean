-- Prove2me | solution 1 for ShortestGCS.Relax.lemma_7_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:27:55.961212+00:00
-- url     : https://prove2.me/submissions/d7a1fd9d-bba6-4344-b9ed-567becf63973

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

namespace RRAux_ShortestGCS_Relax_lemma_7_4

open Matrix ShortestGCS.Relax Filter Topology

lemma vmv {n m : ℕ} (x : Fin n → ℝ) (y c : Fin m → ℝ) : vecMulVec x y *ᵥ c = (y ⬝ᵥ c) • x := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma dual_rep {n : ℕ} (F : StrongDual ℝ (Fin n → ℝ)) :
    ∃ a : Fin n → ℝ, ∀ z, F z = a ⬝ᵥ z := by
  classical
  refine ⟨fun i => F (fun j => if i = j then 1 else 0), fun z => ?_⟩
  have := LinearMap.pi_apply_eq_sum_univ (F : (Fin n → ℝ) →ₗ[ℝ] ℝ) z
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [this, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]

lemma mem_of_relax {n m : ℕ} (X : Set (Fin n → ℝ)) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (Y : Set (Fin m → ℝ)) (x : Fin n → ℝ) (y : Fin m → ℝ) (Z : Matrix (Fin n) (Fin m) ℝ)
    (h : (x, y, Z) ∈ relaxSet X Y) : x ∈ X := by
  by_contra hx
  obtain ⟨F, u, hFx, hFX⟩ := geometric_hahn_banach_point_closed hXcv hXc.isClosed hx
  obtain ⟨a, ha⟩ := dual_rep F
  have hab : (a, -u) ∈ validCone X := fun z hz => by
    have := hFX z hz; rw [ha] at this; simp only; linarith
  have hcd : ((0 : Fin m → ℝ), (1 : ℝ)) ∈ validCone Y := fun z _ => by simp
  have := h _ hab _ hcd
  simp only [mulVec_zero, dotProduct_zero, zero_dotProduct, one_mul, mul_zero, add_zero,
    mul_one] at this
  rw [ha] at hFx
  linarith

lemma kills {n m : ℕ} (X : Set (Fin n → ℝ)) (hXc : IsCompact X)
    (Y : Set (Fin m → ℝ)) (x : Fin n → ℝ) (y : Fin m → ℝ) (Z : Matrix (Fin n) (Fin m) ℝ)
    (h : (x, y, Z) ∈ relaxSet X Y) (c : Fin m → ℝ) (d : ℝ) (hcd : (c, d) ∈ validCone Y)
    (hact : c ⬝ᵥ y + d = 0) : Z *ᵥ c + d • x = 0 := by
  set v := Z *ᵥ c + d • x
  have hall : ∀ a : Fin n → ℝ, 0 ≤ a ⬝ᵥ v := by
    intro a
    obtain ⟨L, hL⟩ := hXc.bddBelow_image (f := fun z => a ⬝ᵥ z) (by fun_prop)
    have hab : (a, -L) ∈ validCone X := fun z hz => by
      have := hL ⟨z, hz, rfl⟩; simp only; linarith
    have := h _ hab _ hcd
    simp only at this
    have e : a ⬝ᵥ (Z *ᵥ c) + d * (a ⬝ᵥ x) + -L * (c ⬝ᵥ y) + -L * d
        = a ⬝ᵥ v + -L * (c ⬝ᵥ y + d) := by
      simp only [v, dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
    rw [e, hact, mul_zero, add_zero] at this
    exact this
  have := hall (-v)
  rw [neg_dotProduct] at this
  have hv : v ⬝ᵥ v = 0 := le_antisymm (by linarith) (by
    have := dotProduct_star_self_nonneg v; rwa [star_trivial] at this)
  exact dotProduct_self_eq_zero.1 hv

lemma span_of_extreme {m : ℕ} {ι : Type*} [Fintype ι] (c : ι → Fin m → ℝ) (d : ι → ℝ)
    (yhat : Fin m → ℝ) (hyhat : yhat ∈ Set.extremePoints ℝ (polyhedron c d))
    (v : Fin m → ℝ) (hv : ∀ i, c i ⬝ᵥ yhat + d i = 0 → c i ⬝ᵥ v = 0) : v = 0 := by
  rw [mem_extremePoints] at hyhat
  obtain ⟨hyY, hext⟩ := hyhat
  have hev : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ i, 0 < c i ⬝ᵥ yhat + d i →
      0 < c i ⬝ᵥ yhat + d i + ε * (c i ⬝ᵥ v) ∧ 0 < c i ⬝ᵥ yhat + d i - ε * (c i ⬝ᵥ v) := by
    rw [eventually_all]
    intro i
    by_cases hi : 0 < c i ⬝ᵥ yhat + d i
    · have t1 : Tendsto (fun ε : ℝ => c i ⬝ᵥ yhat + d i + ε * (c i ⬝ᵥ v)) (𝓝 0)
          (𝓝 (c i ⬝ᵥ yhat + d i + 0 * (c i ⬝ᵥ v))) :=
        tendsto_const_nhds.add (tendsto_id.mul_const _)
      have t2 : Tendsto (fun ε : ℝ => c i ⬝ᵥ yhat + d i - ε * (c i ⬝ᵥ v)) (𝓝 0)
          (𝓝 (c i ⬝ᵥ yhat + d i - 0 * (c i ⬝ᵥ v))) :=
        tendsto_const_nhds.sub (tendsto_id.mul_const _)
      rw [zero_mul, add_zero] at t1
      rw [zero_mul, sub_zero] at t2
      filter_upwards [t1.eventually (lt_mem_nhds hi), t2.eventually (lt_mem_nhds hi)]
        with ε h1 h2 _
      exact ⟨h1, h2⟩
    · exact Eventually.of_forall fun ε h => absurd h hi
  obtain ⟨ε, hε1, hε2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioi 0)).exists
  have hεpos : 0 < ε := hε2
  have hmem : ∀ s : ℝ, s = ε ∨ s = -ε → yhat + s • v ∈ polyhedron c d := by
    intro s hs i
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    by_cases hi : c i ⬝ᵥ yhat + d i = 0
    · rw [hv i hi, mul_zero, add_zero]; exact hyY i
    · have hpos : 0 < c i ⬝ᵥ yhat + d i := lt_of_le_of_ne (hyY i) (Ne.symm hi)
      obtain ⟨h1, h2⟩ := hε1 i hpos
      rcases hs with rfl | rfl
      · linarith
      · rw [neg_mul]; linarith
  have hseg : yhat ∈ openSegment ℝ (yhat + ε • v) (yhat + (-ε) • v) :=
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by
      rw [neg_smul]; module⟩
  obtain ⟨h1, -⟩ := hext _ (hmem ε (Or.inl rfl)) _ (hmem (-ε) (Or.inr rfl)) hseg
  have : ε • v = 0 := by
    have := congrArg (fun w => w - yhat) h1
    simpa using this
  exact (smul_eq_zero.1 this).resolve_left hεpos.ne'

end RRAux_ShortestGCS_Relax_lemma_7_4

open ShortestGCS.Relax in
theorem solution {n m : ℕ} {ι : Type*} [Fintype ι] (X : Set (Fin n → ℝ)) (hXc : IsCompact X)
    (hXcv : Convex ℝ X) (c : ι → Fin m → ℝ) (d : ι → ℝ)
    (hY : Bornology.IsBounded (polyhedron c d)) (yhat : Fin m → ℝ)
    (hyhat : yhat ∈ Set.extremePoints ℝ (polyhedron c d)) :
    ∀ (x : Fin n → ℝ) (Z : Matrix (Fin n) (Fin m) ℝ),
      (x, yhat, Z) ∈ bilinSet X (polyhedron c d) ↔ (x, yhat, Z) ∈ relaxSet X (polyhedron c d) := by
  open RRAux_ShortestGCS_Relax_lemma_7_4 Matrix in
  intro x Z
  have hyY : yhat ∈ polyhedron c d := hyhat.1
  constructor
  · rintro ⟨hx, -, hZ⟩
    intro ab hab cd hcd
    simp only at hZ ⊢
    rw [hZ, vmv, dotProduct_smul, smul_eq_mul]
    have h1 := hab x hx
    have h2 := hcd yhat hyY
    have e : ab.1 ⬝ᵥ x * (yhat ⬝ᵥ cd.1) + cd.2 * (ab.1 ⬝ᵥ x) + ab.2 * (cd.1 ⬝ᵥ yhat) + ab.2 * cd.2
        = (ab.1 ⬝ᵥ x + ab.2) * (cd.1 ⬝ᵥ yhat + cd.2) := by
      rw [dotProduct_comm yhat cd.1]; ring
    rw [mul_comm (yhat ⬝ᵥ cd.1), e]
    exact mul_nonneg h1 h2
  · intro h
    have hx := mem_of_relax X hXc hXcv _ x yhat Z h
    refine ⟨hx, hyY, ?_⟩
    simp only
    -- W := Z - x yhatᵀ kills every active c i
    have hW : ∀ i, c i ⬝ᵥ yhat + d i = 0 → (Z - vecMulVec x yhat) *ᵥ c i = 0 := by
      intro i hi
      have hcd : (c i, d i) ∈ validCone (polyhedron c d) := fun z hz => hz i
      have hk := kills X hXc _ x yhat Z h (c i) (d i) hcd hi
      rw [sub_mulVec, vmv, dotProduct_comm, show c i ⬝ᵥ yhat = -d i by linarith, neg_smul]
      calc Z *ᵥ c i - -(d i • x) = Z *ᵥ c i + d i • x := by rw [sub_neg_eq_add]
        _ = 0 := hk
    rw [← sub_eq_zero]
    ext k l
    -- row k of W is orthogonal to all active c i
    have hrow := span_of_extreme c d yhat hyhat (fun j => (Z - vecMulVec x yhat) k j)
      (fun i hi => by
        have := congrFun (hW i hi) k
        simpa [mulVec, dotProduct, mul_comm] using this)
    have := congrFun hrow l
    simpa using this

#print axioms solution
