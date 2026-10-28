-- Prove2me | solution 1 for WHAdditivity.Renyi.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:42:32.30152+00:00
-- url     : https://prove2.me/submissions/d1ae5c11-0f32-4030-a188-c6cd76458df4

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

open WHAdditivity.Renyi Matrix
open scoped ComplexOrder

section helpers
open Classical

/-- site condition for `tensorIdentity Λ (reducedMatrix Λ ρ)` -/
def cnd {N : ℕ} (Λ : Finset (Fin N)) (j : Fin N) {α : Type} (a b u v : α) : Prop :=
  (j ∈ Λ → u = a ∧ v = b) ∧ (j ∉ Λ → a = b ∧ u = v)

lemma restrict_eq_iff {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (z y : Config d) :
    restrict d Λ z = restrict d Λ y ↔ ∀ j ∈ Λ, z j = y j := by
  simp [restrict, funext_iff]

lemma restrict_eq_iff' {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (z : Config d)
    (a : SubConfig d Λ) :
    restrict d Λ z = a ↔ ∀ j (h : j ∈ Λ), z j = a ⟨j, h⟩ := by
  simp [restrict, funext_iff]

lemma tI_apply {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (ρ : Matrix (Config d) (Config d) ℂ)
    (y y' : Config d) :
    tensorIdentity d Λ (reducedMatrix d Λ ρ) y y' =
      ∑ z : Config d, ∑ z' : Config d,
        if (∀ j, cnd Λ j (y j) (y' j) (z j) (z' j)) then ρ z z' else 0 := by
  unfold tensorIdentity reducedMatrix
  simp only [Matrix.of_apply]
  split_ifs with h
  · apply Finset.sum_congr rfl; intro z _; apply Finset.sum_congr rfl; intro z' _
    have : (restrict d Λ z = restrict d Λ y ∧ restrict d Λ z' = restrict d Λ y' ∧
        ∀ j, j ∉ Λ → z j = z' j) ↔ ∀ j, cnd Λ j (y j) (y' j) (z j) (z' j) := by
      rw [restrict_eq_iff, restrict_eq_iff]
      constructor
      · rintro ⟨h1, h2, h3⟩ j
        exact ⟨fun hj => ⟨h1 j hj, h2 j hj⟩, fun hj => ⟨h j hj, h3 j hj⟩⟩
      · intro hc
        exact ⟨fun j hj => ((hc j).1 hj).1, fun j hj => ((hc j).1 hj).2,
          fun j hj => ((hc j).2 hj).2⟩
    by_cases hc : ∀ j, cnd Λ j (y j) (y' j) (z j) (z' j)
    · rw [if_pos (this.mpr hc), if_pos hc]
    · rw [if_neg (fun h' => hc (this.mp h')), if_neg hc]
  · symm; apply Finset.sum_eq_zero; intro z _; apply Finset.sum_eq_zero; intro z' _
    rw [if_neg]; intro hc; exact h fun j hj => ((hc j).2 hj).1

lemma count_pi {N : ℕ} (d : Fin N → ℕ) (g : (j : Fin N) → Fin (d j) → Fin (d j) → ℂ) :
    (∑ y : Config d, ∑ y' : Config d, ∏ j, g j (y j) (y' j)) =
      ∏ j, ∑ a : Fin (d j), ∑ b : Fin (d j), g j a b := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl; intro y _
  rw [Fintype.prod_sum]

lemma sum2_single {α β : Type} [Fintype α] [Fintype β] (f : α → β → ℂ) (u : α) (v : β)
    (hQ : ∀ a b, f a b ≠ 0 → a = u ∧ b = v) :
    (∑ a, ∑ b, f a b) = f u v := by
  rw [Finset.sum_eq_single u, Finset.sum_eq_single v]
  · intro b _ hb; by_contra h; exact hb (hQ _ _ h).2
  · simp
  · intro a _ ha; apply Finset.sum_eq_zero; intro b _; by_contra h; exact ha (hQ _ _ h).1
  · simp

lemma ite_ne_zero_imp {P : Prop} [Decidable P] (h : (if P then (1:ℂ) else 0) ≠ 0) : P := by
  by_contra hP; exact h (if_neg hP)

lemma site_count {N : ℕ} (Λ Λ' : Finset (Fin N)) (j : Fin N) (n : ℕ) (u v s t : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n,
      if (cnd Λ j a b u v ∧ cnd Λ' j b a s t) then (1:ℂ) else 0) =
    (if j ∈ (Λ ∪ Λ')ᶜ then (n:ℂ) else 1) *
      (if ((j ∈ Λ ∩ Λ' → s = v ∧ t = u) ∧ (j ∉ Λ ∩ Λ' → u = v ∧ s = t)) then 1 else 0) := by
  by_cases hj : j ∈ Λ <;> by_cases hj' : j ∈ Λ'
  · rw [sum2_single _ u v (by intro a b h; have h := ite_ne_zero_imp h; simp [cnd, hj, hj'] at h; exact ⟨h.1.1.symm, h.1.2.symm⟩)]
    simp [cnd, hj, hj']
  · rw [sum2_single _ u v (by intro a b h; have h := ite_ne_zero_imp h; simp [cnd, hj, hj'] at h; exact ⟨h.1.1.symm, h.1.2.symm⟩)]
    simp [cnd, hj, hj']
    by_cases h1 : u = v <;> by_cases h2 : s = t <;> simp [h1, h2, eq_comm]
  · rw [sum2_single _ t s (by intro a b h; have h := ite_ne_zero_imp h; simp [cnd, hj, hj'] at h; exact ⟨h.2.2.symm, h.2.1.symm⟩)]
    simp [cnd, hj, hj']
    by_cases h1 : u = v <;> by_cases h2 : s = t <;> simp [h1, h2, eq_comm]
  · have : ∀ a : Fin n, (∑ b : Fin n, if (cnd Λ j a b u v ∧ cnd Λ' j b a s t) then (1:ℂ) else 0)
        = if (u = v ∧ s = t) then 1 else 0 := by
      intro a
      rw [Finset.sum_eq_single a]
      · simp [cnd, hj, hj']
      · intro b _ hb; rw [if_neg]; intro h; simp [cnd, hj, hj'] at h; exact hb h.1.1.symm
      · simp
    rw [Finset.sum_congr rfl (fun a _ => this a)]
    simp [hj, hj']

lemma pull5 {α β γ δ ε : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    (f : α → β → γ → δ → ε → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]

lemma pull6 {α β γ δ ε ζ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    [Fintype ζ] (f : α → β → γ → δ → ε → ζ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g) = ∑ c, ∑ d, ∑ e, ∑ g, ∑ a, ∑ b, f a b c d e g := by
  rw [Finset.sum_congr rfl (fun a _ => pull5 (f a))]
  exact pull5 (fun a c d e g => ∑ b, f a b c d e g)

def hcnd {N : ℕ} (Λ Λ' : Finset (Fin N)) (j : Fin N) {α : Type} (u v s t : α) : Prop :=
  (j ∈ Λ ∩ Λ' → s = v ∧ t = u) ∧ (j ∉ Λ ∩ Λ' → u = v ∧ s = t)

lemma lhs_point {N : ℕ} (d : Fin N → ℕ) (ρ : Matrix (Config d) (Config d) ℂ)
    (Λ Λ' : Finset (Fin N)) (z z' w w' : Config d) :
    (∑ y : Config d, ∑ y' : Config d,
      (if (∀ j, cnd Λ j (y j) (y' j) (z j) (z' j)) then ρ z z' else 0) *
      (if (∀ j, cnd Λ' j (y' j) (y j) (w j) (w' j)) then ρ w w' else 0)) =
    ρ z z' * ρ w w' * ((∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) *
      (if ∀ j, hcnd Λ Λ' j (z j) (z' j) (w j) (w' j) then 1 else 0)) := by
  have e1 : ∀ y y' : Config d,
      (if (∀ j, cnd Λ j (y j) (y' j) (z j) (z' j)) then ρ z z' else 0) *
      (if (∀ j, cnd Λ' j (y' j) (y j) (w j) (w' j)) then ρ w w' else 0) =
      ρ z z' * ρ w w' * ∏ j, (if (cnd Λ j (y j) (y' j) (z j) (z' j) ∧
          cnd Λ' j (y' j) (y j) (w j) (w' j)) then (1:ℂ) else 0) := by
    intro y y'
    by_cases h1 : ∀ j, cnd Λ j (y j) (y' j) (z j) (z' j) <;>
      by_cases h2 : ∀ j, cnd Λ' j (y' j) (y j) (w j) (w' j)
    · rw [if_pos h1, if_pos h2, Finset.prod_eq_one (fun j _ => if_pos ⟨h1 j, h2 j⟩)]; ring
    · push Not at h2; obtain ⟨j, hj⟩ := h2
      rw [if_pos h1, if_neg (by push Not; exact ⟨j, hj⟩),
        Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (fun h => hj h.2))]; ring
    · push Not at h1; obtain ⟨j, hj⟩ := h1
      rw [if_neg (by push Not; exact ⟨j, hj⟩),
        Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (fun h => hj h.1))]; ring
    · push Not at h1; obtain ⟨j, hj⟩ := h1
      rw [if_neg (by push Not; exact ⟨j, hj⟩),
        Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (fun h => hj h.1))]; ring
  simp_rw [e1, ← Finset.mul_sum]
  congr 1
  rw [count_pi d (fun j a b => if (cnd Λ j a b (z j) (z' j) ∧ cnd Λ' j b a (w j) (w' j)) then (1:ℂ) else 0)]
  rw [Finset.prod_congr rfl (fun j _ => site_count Λ Λ' j (d j) (z j) (z' j) (w j) (w' j))]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Fintype.prod_boole]
  congr 1
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; exact h2 h1) | (exfalso; exact h1 h2)

lemma rM_apply {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (ρ : Matrix (Config d) (Config d) ℂ)
    (a b : SubConfig d Λ) :
    reducedMatrix d Λ ρ a b = ∑ z : Config d, ∑ z' : Config d,
      if (restrict d Λ z = a ∧ restrict d Λ z' = b ∧ (∀ j, j ∉ Λ → z j = z' j)) then ρ z z' else 0 := by
  unfold reducedMatrix; simp only [Matrix.of_apply]

lemma rhs_point {N : ℕ} (d : Fin N → ℕ) (ρ : Matrix (Config d) (Config d) ℂ)
    (Λ Λ' : Finset (Fin N)) (z z' w w' : Config d) :
    (∑ a : SubConfig d (Λ ∩ Λ'), ∑ a' : SubConfig d (Λ ∩ Λ'),
      (if (restrict d (Λ ∩ Λ') z = a ∧ restrict d (Λ ∩ Λ') z' = a' ∧
          (∀ j, j ∉ Λ ∩ Λ' → z j = z' j)) then ρ z z' else 0) *
      (if (restrict d (Λ ∩ Λ') w = a' ∧ restrict d (Λ ∩ Λ') w' = a ∧
          (∀ j, j ∉ Λ ∩ Λ' → w j = w' j)) then ρ w w' else 0)) =
    ρ z z' * ρ w w' * (if ∀ j, hcnd Λ Λ' j (z j) (z' j) (w j) (w' j) then 1 else 0) := by
  rw [sum2_single _ (restrict d (Λ ∩ Λ') z) (restrict d (Λ ∩ Λ') z')]
  · have key : ((∀ j, j ∉ Λ ∩ Λ' → z j = z' j) ∧ restrict d (Λ ∩ Λ') w = restrict d (Λ ∩ Λ') z' ∧
        restrict d (Λ ∩ Λ') w' = restrict d (Λ ∩ Λ') z ∧ (∀ j, j ∉ Λ ∩ Λ' → w j = w' j)) ↔
        ∀ j, hcnd Λ Λ' j (z j) (z' j) (w j) (w' j) := by
      rw [restrict_eq_iff, restrict_eq_iff]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩ j
        exact ⟨fun hj => ⟨h2 j hj, h3 j hj⟩, fun hj => ⟨h1 j hj, h4 j hj⟩⟩
      · intro h
        exact ⟨fun j hj => ((h j).2 hj).1, fun j hj => ((h j).1 hj).1,
          fun j hj => ((h j).1 hj).2, fun j hj => ((h j).2 hj).2⟩
    by_cases hk : ∀ j, hcnd Λ Λ' j (z j) (z' j) (w j) (w' j)
    · obtain ⟨h1, h2, h3, h4⟩ := key.mpr hk
      rw [if_pos ⟨rfl, rfl, h1⟩, if_pos ⟨h2, h3, h4⟩, if_pos hk]; ring
    · rw [if_neg hk, mul_zero]
      by_cases h1 : ∀ j, j ∉ Λ ∩ Λ' → z j = z' j
      · rw [if_pos ⟨rfl, rfl, h1⟩, if_neg (fun h => hk (key.mp ⟨h1, h.1, h.2.1, h.2.2⟩)), mul_zero]
      · rw [if_neg (fun h => h1 h.2.2), zero_mul]
  · intro a b h
    by_contra hc
    apply h
    have : ¬ (restrict d (Λ ∩ Λ') z = a ∧ restrict d (Λ ∩ Λ') z' = b ∧
          (∀ j, j ∉ Λ ∩ Λ' → z j = z' j)) := fun h' => hc ⟨h'.1.symm, h'.2.1.symm⟩
    rw [if_neg this, zero_mul]



lemma trace_cfc_herm {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp_def]

lemma traceRpow_eq {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (p : ℝ) :
    traceRpow p A = ∑ i, hA.eigenvalues i ^ p := by
  unfold traceRpow; rw [trace_cfc_herm hA]
  rw [Complex.re_sum]; simp

lemma vN_eq {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) :
    vonNeumannEntropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  unfold vonNeumannEntropy; rw [trace_cfc_herm hA]
  rw [Complex.re_sum]; simp


lemma rev3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun b _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

def Mred {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (v : Config d → ℂ) :
    Matrix (SubConfig d Λ) (SubConfig d Λᶜ) ℂ :=
  Matrix.of fun a w => ∑ z : Config d,
    if restrict d Λ z = a ∧ restrict d Λᶜ z = w then v z else 0

lemma rM_eq_MM {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (v : Config d → ℂ) :
    reducedMatrix d Λ (pureState v) = Mred d Λ v * (Mred d Λ v)ᴴ := by
  ext a b
  rw [rM_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Mred, Matrix.of_apply, star_sum,
    Finset.sum_mul, Finset.mul_sum, pureState, Matrix.vecMulVec_apply, Pi.star_apply]
  rw [rev3]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  rw [Finset.sum_eq_single (restrict d Λᶜ z)]
  · have hc : restrict d Λᶜ z = restrict d Λᶜ z' ↔ ∀ j, j ∉ Λ → z j = z' j := by
      rw [restrict_eq_iff]; simp
    by_cases h1 : restrict d Λ z = a <;> by_cases h2 : restrict d Λ z' = b <;>
      by_cases h3 : ∀ j, j ∉ Λ → z j = z' j <;> simp [h1, h2, h3, hc, eq_comm]
    all_goals rw [if_pos h3, if_pos h3]
  · intro w _ hw
    by_cases h1 : restrict d Λ z = a ∧ restrict d Λᶜ z = w
    · exact absurd h1.2.symm hw
    · rw [if_neg h1, zero_mul]
  · simp

lemma rM_psd {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (v : Config d → ℂ) :
    (reducedMatrix d Λ (pureState v)).PosSemidef := by
  rw [rM_eq_MM]; exact Matrix.posSemidef_self_mul_conjTranspose _

lemma rM_trace {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (ρ : Matrix (Config d) (Config d) ℂ) :
    (reducedMatrix d Λ ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, rM_apply]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun z _ => ?_)
  rw [Finset.sum_comm]
  have : ∀ z' : Config d, (∑ a : SubConfig d Λ, if (restrict d Λ z = a ∧ restrict d Λ z' = a ∧
      (∀ j, j ∉ Λ → z j = z' j)) then ρ z z' else 0) = if z = z' then ρ z z' else 0 := by
    intro z'
    rw [Finset.sum_eq_single (restrict d Λ z)]
    · by_cases h : z = z'
      · subst h; rw [if_pos ⟨rfl, rfl, fun _ _ => rfl⟩, if_pos rfl]
      · rw [if_neg h, if_neg]
        rintro ⟨-, h2, h3⟩
        apply h; funext j
        by_cases hj : j ∈ Λ
        · exact ((restrict_eq_iff d Λ z' z).mp h2 j hj).symm
        · exact h3 j hj
    · intro a _ ha; rw [if_neg]; rintro ⟨h1, -⟩; exact ha h1.symm
    · simp
  rw [Finset.sum_congr rfl fun z' _ => this z', Finset.sum_ite_eq]
  simp

lemma pure_density {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (hv : IsUnitVector v) :
    IsDensity (pureState v) := by
  refine ⟨?_, ?_⟩
  · unfold pureState
    have : Matrix.vecMulVec v (star v) = Matrix.replicateCol Unit v * (Matrix.replicateCol Unit v)ᴴ := by
      ext i j; simp [Matrix.vecMulVec_apply, Matrix.mul_apply]
    rw [this]; exact Matrix.posSemidef_self_mul_conjTranspose _
  · unfold pureState IsUnitVector at *
    simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply]
    have : ∀ i, v i * star (v i) = ((Complex.normSq (v i) : ℝ) : ℂ) := fun i => Complex.mul_conj _
    simp_rw [this]; rw [← Complex.ofReal_sum, hv]; simp

lemma rM_density {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (v : Config d → ℂ)
    (hv : IsUnitVector v) : IsDensity (reducedMatrix d Λ (pureState v)) :=
  ⟨rM_psd d Λ v, by rw [rM_trace]; exact (pure_density v hv).2⟩

lemma trace_sq_density {ι : Type} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ}
    (hP : IsDensity P) :
    ∃ r : ℝ, (P ^ 2).trace = (r : ℂ) ∧ 0 ≤ r ∧ r ≤ 1 := by
  have hH := hP.1.isHermitian
  have h0 : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hP.1.eigenvalues_nonneg i
  have h1 : ∑ i, hH.eigenvalues i = 1 := by
    have h := hH.trace_eq_sum_eigenvalues
    have h2 : P.trace = 1 := hP.2
    have := congrArg Complex.re (h2.symm.trans h)
    simp [Complex.re_sum] at this
    linarith
  refine ⟨∑ i, hH.eigenvalues i ^ 2, ?_, ?_, ?_⟩
  · have hc : cfc (fun x : ℝ => x ^ 2) P = P ^ 2 := cfc_pow_id P 2 hH.isSelfAdjoint
    rw [← hc, trace_cfc_herm hH]; push_cast; rfl
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · calc ∑ i, hH.eigenvalues i ^ 2 ≤ ∑ i, hH.eigenvalues i := by
          apply Finset.sum_le_sum; intro i _
          have : hH.eigenvalues i ≤ 1 := h1 ▸ Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
          nlinarith [h0 i]
      _ = 1 := h1

lemma wh_single (n : ℕ) (a b u v : Fin n) :
    wernerHolevo n (Matrix.single a b 1) u v =
      ((n : ℂ) - 1)⁻¹ * ((if (a = b ∧ u = v) then 1 else 0) - (if (u = b ∧ v = a) then 1 else 0)) := by
  unfold wernerHolevo
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply, Matrix.single_apply,
    smul_eq_mul, Matrix.one_apply]
  congr 1
  by_cases hab : a = b
  · subst hab; rw [Matrix.trace_single_eq_same]
    by_cases huv : u = v <;> simp [huv, eq_comm, and_comm]
  · rw [Matrix.trace_single_eq_of_ne _ _ _ hab]
    simp [hab, eq_comm, and_comm]

lemma prod_split {N : ℕ} (d : Fin N → ℕ) (y y' x x' : Config d) :
    (∏ j, wernerHolevo (d j) (Matrix.single (x j) (x' j) 1) (y j) (y' j)) =
      (∏ j, ((d j : ℂ) - 1)⁻¹) * ∑ t : Finset (Fin N), (-1 : ℂ) ^ t.card *
        (if ∀ j, cnd t j (y j) (y' j) (x' j) (x j) then 1 else 0) := by
  simp_rw [wh_single]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp_rw [sub_eq_neg_add]
  rw [Finset.prod_add, Finset.powerset_univ]
  apply Finset.sum_congr rfl; intro t _
  rw [Finset.prod_neg, mul_assoc]
  congr 1
  have : (∏ j ∈ t, (if (y j = x' j ∧ y' j = x j) then (1:ℂ) else 0)) *
      ∏ j ∈ Finset.univ \ t, (if (x j = x' j ∧ y j = y' j) then (1:ℂ) else 0) =
      ∏ j, (if cnd t j (y j) (y' j) (x' j) (x j) then (1:ℂ) else 0) := by
    rw [← Finset.prod_sdiff (Finset.subset_univ t) (f := fun j => if cnd t j (y j) (y' j) (x' j) (x j) then (1:ℂ) else 0), mul_comm]
    congr 1
    · apply Finset.prod_congr rfl; intro j hj
      have hj : j ∉ t := (Finset.mem_sdiff.mp hj).2
      by_cases h : x j = x' j ∧ y j = y' j
      · rw [if_pos h, if_pos]; exact ⟨fun hj' => absurd hj' hj, fun _ => ⟨h.2, h.1.symm⟩⟩
      · rw [if_neg h, if_neg]; intro hc; exact h ⟨((hc.2 hj).2).symm, (hc.2 hj).1⟩
    · apply Finset.prod_congr rfl; intro j hj
      by_cases h : y j = x' j ∧ y' j = x j
      · rw [if_pos h, if_pos]; exact ⟨fun _ => ⟨h.1.symm, h.2.symm⟩, fun hj' => absurd hj hj'⟩
      · rw [if_neg h, if_neg]; intro hc; exact h ⟨((hc.1 hj).1).symm, ((hc.1 hj).2).symm⟩
  rw [this]; convert Fintype.prod_boole (M₀ := ℂ)

theorem expansion_aux (N : ℕ) (d : Fin N → ℕ) (Ω : Config d → ℂ) :
    tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω) =
      (∏ j, ((d j : ℂ) - 1)⁻¹) • ∑ Λ : Finset (Fin N),
        ((-1 : ℂ) ^ Λ.card) • tensorIdentity d Λ (reducedMatrix d Λ (pureState (star Ω))) := by
  ext y y'
  simp only [tensorChannel, Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    tI_apply, prod_split]
  simp only [pureState, Matrix.vecMulVec_apply, Pi.star_apply, star_star]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring


theorem tmp_aux (N : ℕ) (d : Fin N → ℕ) (ρ : Matrix (Config d) (Config d) ℂ)
    (Λ Λ' : Finset (Fin N)) :
    (tensorIdentity d Λ (reducedMatrix d Λ ρ) * tensorIdentity d Λ' (reducedMatrix d Λ' ρ)).trace =
      (∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) * (reducedMatrix d (Λ ∩ Λ') ρ ^ 2).trace := by
  have hL : (tensorIdentity d Λ (reducedMatrix d Λ ρ) *
      tensorIdentity d Λ' (reducedMatrix d Λ' ρ)).trace =
      ∑ z : Config d, ∑ z' : Config d, ∑ w : Config d, ∑ w' : Config d,
        ρ z z' * ρ w w' * ((∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) *
          (if ∀ j, hcnd Λ Λ' j (z j) (z' j) (w j) (w' j) then 1 else 0)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, tI_apply]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [pull6]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ =>
      Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
    rw [← lhs_point d ρ Λ Λ' z z' w w']
  have hR : (reducedMatrix d (Λ ∩ Λ') ρ ^ 2).trace =
      ∑ z : Config d, ∑ z' : Config d, ∑ w : Config d, ∑ w' : Config d,
        ρ z z' * ρ w w' * (if ∀ j, hcnd Λ Λ' j (z j) (z' j) (w j) (w' j) then 1 else 0) := by
    rw [pow_two]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, rM_apply]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [pull6]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ =>
      Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
    rw [← rhs_point d ρ Λ Λ' z z' w w']
  rw [hL, hR]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ =>
      Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
  ring

lemma alt_sum {N : ℕ} (T : Finset (Fin N)) (g : Fin N → ℂ) :
    (∑ t ∈ T.powerset, (-1 : ℂ) ^ t.card * ∏ j ∈ T \ t, g j) = ∏ j ∈ T, (g j - 1) := by
  have := Finset.prod_add (fun _ => (-1 : ℂ)) g T
  simp only [Finset.prod_const] at this
  rw [← this]; apply Finset.prod_congr rfl; intro j _; ring

lemma sum_compl_prod {N : ℕ} (g : Fin N → ℝ) :
    (∑ t : Finset (Fin N), ∏ j ∈ tᶜ, g j) = ∏ j, (1 + g j) := by
  rw [Finset.prod_add, Finset.powerset_univ]
  apply Finset.sum_congr rfl; intro t _
  simp [Finset.compl_eq_univ_sdiff]

lemma double_alt {N : ℕ} (S : Finset (Fin N)) (d : Fin N → ℂ) :
    (∑ Δ ∈ S.powerset, (-1 : ℂ) ^ Δ.card *
      ∑ Δ' ∈ (S \ Δ).powerset, (-1 : ℂ) ^ Δ'.card * ∏ j ∈ (S \ Δ) \ Δ', d j) =
    ∏ j ∈ S, (d j - 2) := by
  simp_rw [alt_sum]
  apply Finset.prod_congr rfl; intro j _; ring

lemma regroup {N : ℕ} (K : Finset (Fin N)) (g : Finset (Fin N) → Finset (Fin N) → ℂ) :
    (∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N), if Λ ∩ Λ' = K then g Λ Λ' else 0) =
    ∑ Δ ∈ Kᶜ.powerset, ∑ Δ' ∈ (Kᶜ \ Δ).powerset, g (K ∪ Δ) (K ∪ Δ') := by
  rw [← Finset.sum_product' (f := fun Λ Λ' => if Λ ∩ Λ' = K then g Λ Λ' else 0),
    ← Finset.sum_filter]
  rw [Finset.sum_sigma' (Kᶜ.powerset) (fun Δ => (Kᶜ \ Δ).powerset) (fun Δ Δ' => g (K ∪ Δ) (K ∪ Δ'))]
  refine Finset.sum_bij' (fun p _ => ⟨p.1 \ p.2, p.2 \ p.1⟩) (fun q _ => (K ∪ q.1, K ∪ q.2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_product, true_and] at hp
    simp only [Finset.mem_sigma, Finset.mem_powerset]
    subst hp
    constructor
    · intro x; simp; tauto
    · intro x; simp; tauto
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hq
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_product, true_and]
    obtain ⟨h1, h2⟩ := hq
    ext x
    have a1 := @h1 x; have a2 := @h2 x
    simp at a1 a2 ⊢; tauto
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_product, true_and] at hp
    subst hp
    ext x <;> simp <;> tauto
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hq
    obtain ⟨h1, h2⟩ := hq
    have e1 : (K ∪ q.1) \ (K ∪ q.2) = q.1 := by
      ext x; have a1 := @h1 x; have a2 := @h2 x; simp at a1 a2 ⊢; tauto
    have e2 : (K ∪ q.2) \ (K ∪ q.1) = q.2 := by
      ext x; have a1 := @h1 x; have a2 := @h2 x; simp at a1 a2 ⊢; tauto
    simp only [e1, e2]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_product, true_and] at hp
    subst hp
    have e1 : p.1 ∩ p.2 ∪ p.1 \ p.2 = p.1 := by ext x; simp; tauto
    have e2 : p.1 ∩ p.2 ∪ p.2 \ p.1 = p.2 := by ext x; simp; tauto
    simp only [e1, e2]

lemma unit_star {ι : Type} [Fintype ι] (φ : ι → ℂ) (hφ : IsUnitVector φ) :
    IsUnitVector (star φ) := by
  unfold IsUnitVector at *; simpa using hφ

theorem eq8_aux (N : ℕ) (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (Ω : Config d → ℂ)
    (hΩ : IsUnitVector Ω) :
    let X := tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω)
    let ρ := pureState (star Ω)
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N),
          (-1 : ℂ) ^ (Λ.card + Λ'.card) *
            (tensorIdentity d Λ (reducedMatrix d Λ ρ) *
              tensorIdentity d Λ' (reducedMatrix d Λ' ρ)).trace ∧
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N),
          (-1 : ℂ) ^ (Λ.card + Λ'.card) *
            ((∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) * (reducedMatrix d (Λ ∩ Λ') ρ ^ 2).trace) ∧
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N),
          (reducedMatrix d Λ ρ ^ 2).trace *
            ∑ Δ ∈ Λᶜ.powerset, (-1 : ℂ) ^ Δ.card *
              ∑ Δ' ∈ (Λᶜ \ Δ).powerset, (-1 : ℂ) ^ Δ'.card *
                ∏ j ∈ (Λᶜ \ Δ) \ Δ', (d j : ℂ) ∧
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N),
          (reducedMatrix d Λ ρ ^ 2).trace * ∏ j ∈ Λᶜ, ((d j : ℂ) - 2) ∧
    (X * X).trace.im = 0 ∧
    (X * X).trace.re ≤ ∏ j, ((d j : ℝ) - 1)⁻¹ := by
  intro X ρ
  set C : ℂ := ∏ j, ((d j : ℂ) - 1)⁻¹ with hC
  have hX : X = C • ∑ Λ : Finset (Fin N),
      ((-1 : ℂ) ^ Λ.card) • tensorIdentity d Λ (reducedMatrix d Λ ρ) := expansion_aux N d Ω
  have hCC : (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) = C * C := by
    rw [hC, ← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro j _; rw [sq, mul_inv]
  have P1 : (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N),
          (-1 : ℂ) ^ (Λ.card + Λ'.card) *
            (tensorIdentity d Λ (reducedMatrix d Λ ρ) *
              tensorIdentity d Λ' (reducedMatrix d Λ' ρ)).trace := by
    rw [hX, hCC, smul_mul_smul_comm, Matrix.trace_smul, Finset.sum_mul_sum, Matrix.trace_sum]
    simp_rw [Matrix.trace_sum, smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul, pow_add]
  have P2 : (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N),
          (-1 : ℂ) ^ (Λ.card + Λ'.card) *
            ((∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) * (reducedMatrix d (Λ ∩ Λ') ρ ^ 2).trace) := by
    rw [P1]; simp_rw [tmp_aux]
  have P3 : (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N),
          (reducedMatrix d Λ ρ ^ 2).trace *
            ∑ Δ ∈ Λᶜ.powerset, (-1 : ℂ) ^ Δ.card *
              ∑ Δ' ∈ (Λᶜ \ Δ).powerset, (-1 : ℂ) ^ Δ'.card *
                ∏ j ∈ (Λᶜ \ Δ) \ Δ', (d j : ℂ) := by
    rw [P2]; congr 1
    set g : Finset (Fin N) → Finset (Fin N) → ℂ := fun Λ Λ' => (-1 : ℂ) ^ (Λ.card + Λ'.card) *
            ((∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) * (reducedMatrix d (Λ ∩ Λ') ρ ^ 2).trace) with hg
    have ha : ∀ Λ Λ', g Λ Λ' = ∑ K : Finset (Fin N), if Λ ∩ Λ' = K then g Λ Λ' else 0 := by
      intro Λ Λ'; rw [Finset.sum_ite_eq]; simp
    calc (∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N), g Λ Λ')
        = ∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N), ∑ K : Finset (Fin N),
            if Λ ∩ Λ' = K then g Λ Λ' else 0 :=
          Finset.sum_congr rfl fun Λ _ => Finset.sum_congr rfl fun Λ' _ => ha Λ Λ'
      _ = ∑ K : Finset (Fin N), ∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N),
            if Λ ∩ Λ' = K then g Λ Λ' else 0 := by
          rw [rev3]; exact Finset.sum_congr rfl fun K _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun K _ => ?_
          rw [regroup, Finset.mul_sum]
          refine Finset.sum_congr rfl fun Δ hΔ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun Δ' hΔ' => ?_
          rw [Finset.mem_powerset] at hΔ hΔ'
          have s1 := @hΔ; have s2 := @hΔ'
          have e1 : (K ∪ Δ) ∩ (K ∪ Δ') = K := by
            ext x; have a1 := @s1 x; have a2 := @s2 x; simp at a1 a2 ⊢; tauto
          have e2 : (K ∪ Δ ∪ (K ∪ Δ'))ᶜ = (Kᶜ \ Δ) \ Δ' := by
            ext x; have a1 := @s1 x; have a2 := @s2 x; simp at a1 a2 ⊢; tauto
          have e3 : (K ∪ Δ).card = K.card + Δ.card := by
            apply Finset.card_union_of_disjoint
            rw [Finset.disjoint_left]; intro x hx hx2; have a1 := @s1 x hx2; simp at a1; exact a1 hx
          have e4 : (K ∪ Δ').card = K.card + Δ'.card := by
            apply Finset.card_union_of_disjoint
            rw [Finset.disjoint_left]; intro x hx hx2; have a2 := @s2 x hx2; simp at a2; exact a2.1 hx
          simp only [hg]; rw [e1, e2, e3, e4]
          rw [show K.card + Δ.card + (K.card + Δ'.card) = 2 * K.card + Δ.card + Δ'.card by ring,
            pow_add, pow_add, pow_mul]
          norm_num; ring
  have P4 : (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N),
          (reducedMatrix d Λ ρ ^ 2).trace * ∏ j ∈ Λᶜ, ((d j : ℂ) - 2) := by
    rw [P3]; congr 1
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [double_alt Kᶜ (fun j => (d j : ℂ))]
  have hr : ∀ K : Finset (Fin N), ∃ r : ℝ, (reducedMatrix d K ρ ^ 2).trace = (r : ℂ) ∧ 0 ≤ r ∧ r ≤ 1 :=
    fun K => trace_sq_density (rM_density d K (star Ω) (unit_star Ω hΩ))
  choose r hr using hr
  set R : ℝ := (∏ j, (((d j : ℝ) - 1) ^ 2)⁻¹) * ∑ K : Finset (Fin N), r K * ∏ j ∈ Kᶜ, ((d j : ℝ) - 2)
    with hRdef
  have hR : (X * X).trace = (R : ℂ) := by
    rw [P4, Finset.sum_congr rfl (fun K _ => by rw [(hr K).1])]
    rw [hRdef]; push_cast; rfl
  have hd1 : ∀ j, (1:ℝ) ≤ (d j : ℝ) - 1 := by
    intro j; have : (2:ℝ) ≤ d j := by exact_mod_cast hd j
    linarith
  refine ⟨P1, P2, P3, P4, by rw [hR, Complex.ofReal_im], ?_⟩
  rw [hR, Complex.ofReal_re, hRdef]
  have hQ : ∀ K : Finset (Fin N), 0 ≤ ∏ j ∈ Kᶜ, ((d j : ℝ) - 2) := by
    intro K; apply Finset.prod_nonneg; intro j _
    have : (2:ℝ) ≤ d j := by exact_mod_cast hd j
    linarith
  have hA : 0 ≤ ∏ j, (((d j : ℝ) - 1) ^ 2)⁻¹ :=
    Finset.prod_nonneg fun j _ => inv_nonneg.mpr (sq_nonneg _)
  calc (∏ j, (((d j : ℝ) - 1) ^ 2)⁻¹) * ∑ K : Finset (Fin N), r K * ∏ j ∈ Kᶜ, ((d j : ℝ) - 2)
      ≤ (∏ j, (((d j : ℝ) - 1) ^ 2)⁻¹) * ∑ K : Finset (Fin N), ∏ j ∈ Kᶜ, ((d j : ℝ) - 2) := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply Finset.sum_le_sum; intro K _
        have := (hr K).2.2
        nlinarith [hQ K]
    _ = (∏ j, (((d j : ℝ) - 1) ^ 2)⁻¹) * ∏ j, ((d j : ℝ) - 1) := by
        rw [sum_compl_prod]; congr 1; apply Finset.prod_congr rfl; intro j _; ring
    _ = ∏ j, ((d j : ℝ) - 1)⁻¹ := by
        rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro j _
        have : (d j : ℝ) - 1 ≠ 0 := by linarith [hd1 j]
        field_simp

theorem solution (N : ℕ) (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (Ω : Config d → ℂ)
    (hΩ : IsUnitVector Ω) :
    let X := tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω)
    let ρ := pureState (star Ω)
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N),
          (-1 : ℂ) ^ (Λ.card + Λ'.card) *
            (tensorIdentity d Λ (reducedMatrix d Λ ρ) *
              tensorIdentity d Λ' (reducedMatrix d Λ' ρ)).trace ∧
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N),
          (-1 : ℂ) ^ (Λ.card + Λ'.card) *
            ((∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) * (reducedMatrix d (Λ ∩ Λ') ρ ^ 2).trace) ∧
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N),
          (reducedMatrix d Λ ρ ^ 2).trace *
            ∑ Δ ∈ Λᶜ.powerset, (-1 : ℂ) ^ Δ.card *
              ∑ Δ' ∈ (Λᶜ \ Δ).powerset, (-1 : ℂ) ^ Δ'.card *
                ∏ j ∈ (Λᶜ \ Δ) \ Δ', (d j : ℂ) ∧
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N),
          (reducedMatrix d Λ ρ ^ 2).trace * ∏ j ∈ Λᶜ, ((d j : ℂ) - 2) ∧
    (X * X).trace.im = 0 ∧
    (X * X).trace.re ≤ ∏ j, ((d j : ℝ) - 1)⁻¹ :=
  eq8_aux N d hd Ω hΩ

end helpers
