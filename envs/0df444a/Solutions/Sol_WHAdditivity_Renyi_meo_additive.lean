-- Prove2me | solution 1 for WHAdditivity.Renyi.meo_additive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:54:26.337136+00:00
-- url     : https://prove2.me/submissions/4767500b-33a1-4f07-b4b0-1d7790f8dd25

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

lemma trace_cfc_of_idem {ι : Type} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (c : ℝ) (hc : c ≠ 0) (hBB : B * B = (c : ℂ) • B) (f : ℝ → ℝ)
    (hf : f 0 = 0) :
    (cfc f B).trace = ((f c / c : ℝ) : ℂ) * B.trace := by
  rw [trace_cfc_herm hB, hB.trace_eq_sum_eigenvalues, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  set l := hB.eigenvalues i
  have hv : (⇑(hB.eigenvectorBasis i) : ι → ℂ) ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 <| hB.eigenvectorBasis.orthonormal.ne_zero i
  have hev := hB.mulVec_eigenvectorBasis i
  have h2 : B *ᵥ (B *ᵥ ⇑(hB.eigenvectorBasis i)) = (c : ℂ) • (B *ᵥ ⇑(hB.eigenvectorBasis i)) := by
    rw [Matrix.mulVec_mulVec, hBB, Matrix.smul_mulVec]
  rw [hev, Matrix.mulVec_smul, hev, smul_smul] at h2
  have h3 : (l * l) • (⇑(hB.eigenvectorBasis i) : ι → ℂ) = (c * l) • ⇑(hB.eigenvectorBasis i) := by
    rw [h2, ← smul_smul]; rw [Complex.coe_smul]
  have h4 : l * l = c * l := smul_left_injective ℝ hv h3
  have : l = 0 ∨ l = c := by
    rcases mul_eq_mul_right_iff.mp h4 with h | h
    · right; exact h
    · left; exact h
  rcases this with h | h
  · rw [h, hf]; simp
  · rw [h]
    have : ((f c / c : ℝ) : ℂ) * (c:ℂ) = f c := by rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hc]
    exact this.symm

lemma pureState_trace {ι : Type} [Fintype ι] (φ : ι → ℂ) (hφ : IsUnitVector φ) :
    (pureState φ).trace = 1 := by
  unfold pureState IsUnitVector at *
  simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply]
  have : ∀ i, φ i * star (φ i) = ((Complex.normSq (φ i) : ℝ) : ℂ) := fun i => Complex.mul_conj _
  simp_rw [this]; rw [← Complex.ofReal_sum, hφ]; simp

lemma pureState_herm {ι : Type} [Fintype ι] (φ : ι → ℂ) : (pureState φ).IsHermitian := by
  unfold pureState; ext i j
  simp [Matrix.vecMulVec_apply, mul_comm]

lemma pureState_idem {ι : Type} [Fintype ι] (φ : ι → ℂ) (hφ : IsUnitVector φ) :
    pureState φ * pureState φ = pureState φ := by
  have ht := pureState_trace φ hφ
  unfold pureState at *
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
  simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply] at ht
  calc ∑ k, φ i * star φ k * (φ k * star φ j) = φ i * star φ j * ∑ k, φ k * star φ k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ = _ := by rw [ht, mul_one]

lemma wh_pure (d : ℕ) (φ : Fin d → ℂ) (hφ : IsUnitVector φ) :
    wernerHolevo d (pureState φ) = ((d : ℂ) - 1)⁻¹ • (1 - pureState (star φ)) := by
  unfold wernerHolevo
  rw [pureState_trace φ hφ, one_smul]
  congr 2
  ext i j; simp [pureState, Matrix.vecMulVec_apply, mul_comm]

lemma renyi_scaled_proj (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1 ≤ p) (ψ : Fin d → ℂ)
    (hψ : IsUnitVector ψ) :
    renyiEntropy p (((d : ℂ) - 1)⁻¹ • (1 - pureState ψ)) = Real.log ((d : ℝ) - 1) := by
  set c : ℝ := ((d : ℝ) - 1)⁻¹ with hc
  have hd1 : (1:ℝ) ≤ (d:ℝ) - 1 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcpos : 0 < c := by rw [hc]; apply inv_pos.mpr; linarith
  have hcC : ((d : ℂ) - 1)⁻¹ = (c : ℂ) := by rw [hc]; push_cast; rfl
  rw [hcC]
  set B := (c : ℂ) • (1 - pureState ψ) with hB
  have hP := pureState_idem ψ hψ
  have hBH : B.IsHermitian := by
    have h1 := (Matrix.isHermitian_one (n := Fin d) (α := ℂ)).sub (pureState_herm ψ)
    rw [hB, Matrix.IsHermitian, Matrix.conjTranspose_smul, h1.eq]; simp
  have hBB : B * B = (c : ℂ) • B := by
    rw [hB, smul_mul_smul_comm, sub_mul, mul_sub, mul_sub, hP, smul_smul]; simp
  have htr : B.trace = 1 := by
    rw [hB, Matrix.trace_smul, Matrix.trace_sub, pureState_trace ψ hψ, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul]
    rw [hc]; push_cast
    have : (d:ℂ) - 1 ≠ 0 := by
      have : ((d:ℝ) - 1 : ℝ) ≠ 0 := by linarith
      exact_mod_cast this
    field_simp
  have hlogc : Real.log c = -Real.log ((d:ℝ) - 1) := by rw [hc, Real.log_inv]
  unfold renyiEntropy
  split_ifs with h1
  · unfold vonNeumannEntropy
    rw [trace_cfc_of_idem hBH c hcpos.ne' hBB _ (Real.negMulLog_zero), htr, mul_one]
    simp only [Complex.ofReal_re]
    rw [Real.negMulLog, hlogc]; field_simp
  · unfold traceRpow
    rw [trace_cfc_of_idem hBH c hcpos.ne' hBB (fun x => x ^ p) (Real.zero_rpow (by intro h; apply h1; linarith)), htr, mul_one]
    simp only [Complex.ofReal_re]
    have : c ^ p / c = c ^ (p - 1) := by
      rw [Real.rpow_sub hcpos, Real.rpow_one]
    rw [this, Real.log_rpow hcpos, hlogc]
    have : (1 - p) ≠ 0 := by intro h; apply h1; linarith
    field_simp; ring

lemma outputEntropies_wh (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1 ≤ p) :
    outputEntropies p (wernerHolevo d) = {Real.log ((d : ℝ) - 1)} := by
  ext s
  simp only [outputEntropies, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    rw [wh_pure d φ hφ]; exact renyi_scaled_proj d hd p hp _ (unit_star φ hφ)
  · rintro rfl
    have h0 : 0 < d := by omega
    refine ⟨Pi.single ⟨0, h0⟩ 1, ?_, ?_⟩
    · unfold IsUnitVector
      rw [Finset.sum_eq_single ⟨0, h0⟩]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    · have hu : IsUnitVector (Pi.single (⟨0, h0⟩ : Fin d) (1:ℂ)) := by
        unfold IsUnitVector
        rw [Finset.sum_eq_single ⟨0, h0⟩]
        · simp
        · intro b _ hb; simp [Pi.single_apply, hb]
        · simp
      rw [wh_pure d _ hu]; exact (renyi_scaled_proj d hd p hp _ (unit_star _ hu)).symm


/-- Real-analytic core: probability vector λ. -/
lemma core_bounds {ι : Type} [Fintype ι] (l : ι → ℝ) (h0 : ∀ i, 0 ≤ l i) (h1 : ∑ i, l i = 1)
    (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    -Real.log (∑ i, l i ^ (2:ℝ)) ≤ (1 - p)⁻¹ * Real.log (∑ i, l i ^ p) ∧
    (1 - p)⁻¹ * Real.log (∑ i, l i ^ p) ≤ ∑ i, Real.negMulLog (l i) := by
  set q := p - 1 with hq
  have hq0 : 0 < q := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hpow : ∀ i, l i ^ p = l i * l i ^ q := by
    intro i
    have : p = 1 + q := by linarith
    rw [this, Real.rpow_add' (h0 i) (by linarith), Real.rpow_one]
  have hsq : ∀ i, l i ^ (2:ℝ) = l i * l i := by
    intro i; rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
  -- positivity of sums
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < l i := by
    by_contra h; push Not at h
    have : ∑ i, l i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (h0 i)
    linarith
  have hTp : 0 < ∑ i, l i ^ p :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hi0 p)
      (Finset.single_le_sum (f := fun i => l i ^ p) (fun i _ => Real.rpow_nonneg (h0 i) p)
        (Finset.mem_univ i0))
  have hT2 : 0 < ∑ i, l i ^ (2:ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hi0 2)
      (Finset.single_le_sum (f := fun i => l i ^ (2:ℝ)) (fun i _ => Real.rpow_nonneg (h0 i) 2)
        (Finset.mem_univ i0))
  -- (A) Jensen with x^q
  have hA : ∑ i, l i ^ p ≤ (∑ i, l i ^ (2:ℝ)) ^ q := by
    have := (Real.concaveOn_rpow hq0.le hq1).le_map_sum (t := Finset.univ) (w := l) (p := l)
      (fun i _ => h0 i) h1 (fun i _ => Set.mem_Ici.mpr (h0 i))
    simp only [smul_eq_mul] at this
    simpa [hpow, hsq] using this
  -- (B) Jensen with log
  have hB : q * ∑ i, l i * Real.log (l i) ≤ Real.log (∑ i, l i ^ p) := by
    set t := Finset.univ.filter (fun i => 0 < l i)
    have hzero : ∀ i, i ∉ t → l i = 0 := by
      intro i hi; simp [t] at hi; exact le_antisymm hi (h0 i)
    have ht1 : ∑ i ∈ t, l i = 1 := by
      rw [← h1]; exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hzero i hi)
    have := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := t) (w := l)
      (p := fun i => l i ^ q) (fun i _ => h0 i) ht1
      (fun i hi => Set.mem_Ioi.mpr (Real.rpow_pos_of_pos (by simpa [t] using hi) q))
    simp only [smul_eq_mul] at this
    have e1 : ∑ i ∈ t, l i * Real.log (l i ^ q) = q * ∑ i, l i * Real.log (l i) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => by simp [hzero i hi])]
      apply Finset.sum_congr rfl; intro i hi
      rw [Real.log_rpow (by simpa [t] using hi)]; ring
    have e2 : ∑ i ∈ t, l i * l i ^ q = ∑ i, l i ^ p := by
      rw [← Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => by simp [hzero i hi, Real.zero_rpow (show p ≠ 0 by linarith)])]
      exact Finset.sum_congr rfl (fun i _ => (hpow i).symm)
    rw [e1, e2] at this; exact this
  have h1p : 1 - p < 0 := by linarith
  constructor
  · -- -log T2 ≤ (1-p)⁻¹ log Tp
    have : Real.log (∑ i, l i ^ p) ≤ q * Real.log (∑ i, l i ^ (2:ℝ)) := by
      rw [← Real.log_rpow hT2]; exact Real.log_le_log hTp hA
    have hrw : (1 - p)⁻¹ * Real.log (∑ i, l i ^ p) = -(Real.log (∑ i, l i ^ p) / q) := by
      rw [hq, div_eq_inv_mul, ← neg_mul, ← inv_neg]; ring_nf
    rw [hrw, neg_le_neg_iff, div_le_iff₀ hq0]; linarith
  · have hS : ∑ i, Real.negMulLog (l i) = -∑ i, l i * Real.log (l i) := by
      simp [Real.negMulLog, Finset.sum_neg_distrib]
    have hrw : (1 - p)⁻¹ * Real.log (∑ i, l i ^ p) = -(Real.log (∑ i, l i ^ p) / q) := by
      rw [hq, div_eq_inv_mul, ← neg_mul, ← inv_neg]; ring_nf
    rw [hS, hrw, neg_le_neg_iff, le_div_iff₀ hq0]; linarith

lemma density_eig {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : IsDensity ρ) :
    (∀ i, 0 ≤ hρ.1.isHermitian.eigenvalues i) ∧ ∑ i, hρ.1.isHermitian.eigenvalues i = 1 := by
  refine ⟨fun i => hρ.1.eigenvalues_nonneg i, ?_⟩
  have h := hρ.1.isHermitian.trace_eq_sum_eigenvalues
  have h2 : ρ.trace = 1 := hρ.2
  have := congrArg Complex.re (h2.symm.trans h)
  simp [Complex.re_sum] at this
  linarith


theorem order_bounds_aux {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ)
    (hρ : IsDensity ρ) (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    renyiEntropy 2 ρ ≤ renyiEntropy p ρ ∧ renyiEntropy p ρ ≤ vonNeumannEntropy ρ := by
  have hH := hρ.1.isHermitian
  obtain ⟨h0, h1⟩ := density_eig hρ
  have h2 : renyiEntropy 2 ρ = -Real.log (∑ i, hH.eigenvalues i ^ (2:ℝ)) := by
    unfold renyiEntropy; rw [if_neg (by norm_num), traceRpow_eq hH]; norm_num
  rcases eq_or_lt_of_le hp1 with rfl | hp
  · have := (core_bounds _ h0 h1 2 (by norm_num) le_rfl).2
    unfold renyiEntropy at *
    rw [if_pos rfl]
    refine ⟨?_, le_rfl⟩
    rw [if_neg (by norm_num), traceRpow_eq hH, vN_eq hH]; exact this
  · have hpe : renyiEntropy p ρ = (1 - p)⁻¹ * Real.log (∑ i, hH.eigenvalues i ^ p) := by
      unfold renyiEntropy; rw [if_neg (by linarith), traceRpow_eq hH]
    rw [h2, hpe, vN_eq hH]
    exact core_bounds _ h0 h1 p hp hp2

/-- Kraus operators of the Werner–Holevo channel (real entries). -/
def Kr (n : ℕ) (q : Fin n × Fin n) (u v : Fin n) : ℝ :=
  (if q = (u, v) then 1 else 0) - (if q = (v, u) then 1 else 0)

lemma kraus_sum (n : ℕ) (u v x x' : Fin n) :
    (∑ q : Fin n × Fin n, Kr n q u x * Kr n q v x') =
      2 * ((if (x = x' ∧ u = v) then 1 else 0) - (if (u = x' ∧ v = x) then 1 else 0)) := by
  simp only [Kr, sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Prod.mk.injEq]
  have e1 : (if u = v ∧ x = x' then (1:ℝ) else 0) = if x = x' ∧ u = v then 1 else 0 := by
    by_cases h : x = x' ∧ u = v
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]
  have e2 : (if x = v ∧ u = x' then (1:ℝ) else 0) = if u = x' ∧ x = v then 1 else 0 := by
    by_cases h : u = x' ∧ x = v
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]
  have e3 : (if u = x' ∧ v = x then (1:ℝ) else 0) = if u = x' ∧ x = v then 1 else 0 := by
    by_cases h : u = x' ∧ x = v
    · rw [if_pos h, if_pos ⟨h.1, h.2.symm⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.symm⟩)]
  rw [e1, e2, e3]; ring

lemma wh_kraus (n : ℕ) (x x' u v : Fin n) :
    wernerHolevo n (Matrix.single x x' 1) u v =
      ((n : ℂ) - 1)⁻¹ * ((1/2 : ℂ) * ∑ q : Fin n × Fin n, (Kr n q u x : ℂ) * (Kr n q v x' : ℂ)) := by
  rw [wh_single]; congr 1
  have h : ∑ q : Fin n × Fin n, (Kr n q u x : ℂ) * (Kr n q v x' : ℂ) =
      ((∑ q : Fin n × Fin n, Kr n q u x * Kr n q v x' : ℝ) : ℂ) := by push_cast; rfl
  rw [h, kraus_sum]
  split_ifs <;> push_cast <;> ring

def wv {N : ℕ} (d : Fin N → ℕ) (Ω : Config d → ℂ) (k : (j : Fin N) → Fin (d j) × Fin (d j))
    (y : Config d) : ℂ :=
  ∑ x : Config d, (∏ j, (Kr (d j) (k j) (y j) (x j) : ℂ)) * Ω x

lemma pure_psd {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    (pureState v).PosSemidef := by
  unfold pureState
  have : Matrix.vecMulVec v (star v) = Matrix.replicateCol Unit v * (Matrix.replicateCol Unit v)ᴴ := by
    ext i j; simp [Matrix.vecMulVec_apply, Matrix.mul_apply]
  rw [this]; exact Matrix.posSemidef_self_mul_conjTranspose _

lemma prod_kraus {N : ℕ} (d : Fin N → ℕ) (y y' x x' : Config d) :
    (∏ j, (((d j : ℂ) - 1)⁻¹ * ((1/2 : ℂ) * ∑ q : Fin (d j) × Fin (d j),
        (Kr (d j) q (y j) (x j) : ℂ) * (Kr (d j) q (y' j) (x' j) : ℂ)))) =
      ((∏ j, (((d j : ℝ) - 1)⁻¹ * (1/2)) : ℝ) : ℂ) *
        ∑ k : (j : Fin N) → Fin (d j) × Fin (d j),
          (∏ j, (Kr (d j) (k j) (y j) (x j) : ℂ)) * (∏ j, (Kr (d j) (k j) (y' j) (x' j) : ℂ)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_sum]
  simp_rw [← Finset.prod_mul_distrib]
  push_cast
  rw [Finset.prod_mul_distrib, mul_assoc]

lemma rot3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => Finset.sum_comm)

lemma tensor_kraus {N : ℕ} (d : Fin N → ℕ) (Ω : Config d → ℂ) :
    tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω) =
      ((∏ j, (((d j : ℝ) - 1)⁻¹ * (1/2)) : ℝ) : ℂ) •
        ∑ k : (j : Fin N) → Fin (d j) × Fin (d j), pureState (wv d Ω k) := by
  ext y y'
  simp only [tensorChannel, Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    wh_kraus, prod_kraus]
  simp only [pureState, Matrix.vecMulVec_apply, Pi.star_apply, wv, star_sum, star_mul',
    star_prod, Complex.star_def, Complex.conj_ofReal]
  simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
  conv_rhs => rw [rot3]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring

lemma tensor_psd {N : ℕ} (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (Ω : Config d → ℂ) :
    (tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω)).PosSemidef := by
  rw [tensor_kraus]
  apply Matrix.PosSemidef.smul
  · exact Matrix.posSemidef_sum _ (fun k _ => pure_psd _)
  · apply Complex.zero_le_real.mpr
    apply Finset.prod_nonneg; intro j _
    have : (2:ℝ) ≤ d j := by exact_mod_cast hd j
    have : 0 ≤ ((d j : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    positivity

lemma wh_trace_single (n : ℕ) (hn : 2 ≤ n) (a b : Fin n) :
    (wernerHolevo n (Matrix.single a b 1)).trace = if a = b then 1 else 0 := by
  unfold wernerHolevo
  rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_transpose, Matrix.trace_one,
    Fintype.card_fin]
  have hn' : (n : ℂ) - 1 ≠ 0 := by
    have : ((n:ℝ) - 1) ≠ 0 := by
      have : (2:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact_mod_cast this
  by_cases h : a = b
  · subst h; rw [Matrix.trace_single_eq_same, if_pos rfl]; simp only [smul_eq_mul]; field_simp
  · rw [Matrix.trace_single_eq_of_ne _ _ _ h, if_neg h]; simp

lemma tensor_trace {N : ℕ} (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (X : Matrix (Config d) (Config d) ℂ) :
    (tensorChannel d (fun j => wernerHolevo (d j)) X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, tensorChannel, Matrix.of_apply]
  rw [rot3]
  have : ∀ x x' : Config d, (∑ y : Config d, X x x' *
      ∏ j, wernerHolevo (d j) (Matrix.single (x j) (x' j) 1) (y j) (y j)) =
      if x = x' then X x x' else 0 := by
    intro x x'
    rw [← Finset.mul_sum, ← Fintype.prod_sum (fun j (a : Fin (d j)) =>
      wernerHolevo (d j) (Matrix.single (x j) (x' j) 1) a a)]
    have h2 : ∀ j, (∑ a : Fin (d j), wernerHolevo (d j) (Matrix.single (x j) (x' j) 1) a a) =
        if x j = x' j then 1 else 0 := fun j => wh_trace_single (d j) (hd j) _ _
    rw [Finset.prod_congr rfl (fun j _ => h2 j), Fintype.prod_boole]
    by_cases h : x = x'
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (funext h')), mul_zero]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => this x x'))]
  simp

lemma tensor_density {N : ℕ} (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (Ω : Config d → ℂ)
    (hΩ : IsUnitVector Ω) :
    IsDensity (tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω)) :=
  ⟨tensor_psd d hd Ω, by rw [tensor_trace d hd]; exact (pure_density Ω hΩ).2⟩

lemma renyi_of_idem {ι : Type} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ}
    (hBH : B.IsHermitian) (c : ℝ) (hcpos : 0 < c) (hBB : B * B = (c : ℂ) • B)
    (htr : B.trace = 1) (p : ℝ) (hp : 1 ≤ p) :
    renyiEntropy p B = -Real.log c := by
  unfold renyiEntropy
  split_ifs with h1
  · unfold vonNeumannEntropy
    rw [trace_cfc_of_idem hBH c hcpos.ne' hBB _ (Real.negMulLog_zero), htr, mul_one]
    simp only [Complex.ofReal_re]
    rw [Real.negMulLog]; field_simp
  · unfold traceRpow
    rw [trace_cfc_of_idem hBH c hcpos.ne' hBB (fun x => x ^ p) (Real.zero_rpow (by intro h; apply h1; linarith)), htr, mul_one]
    simp only [Complex.ofReal_re]
    have : c ^ p / c = c ^ (p - 1) := by
      rw [Real.rpow_sub hcpos, Real.rpow_one]
    rw [this, Real.log_rpow hcpos]
    have : (1 - p) ≠ 0 := by intro h; apply h1; linarith
    field_simp; ring

lemma traceRpow_two {ι : Type} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) : traceRpow 2 P = (P * P).trace.re := by
  unfold traceRpow
  have : cfc (fun x : ℝ => x ^ (2:ℝ)) P = P * P := by
    rw [show (fun x : ℝ => x ^ (2:ℝ)) = (fun x : ℝ => x ^ 2) from funext fun x => Real.rpow_two x,
      cfc_pow_id P 2 hP.isSelfAdjoint, sq]
  rw [this]

lemma trace_sq_pos {ι : Type} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ}
    (hP : IsDensity P) : 0 < (P * P).trace.re := by
  have hH := hP.1.isHermitian
  obtain ⟨h0, h1⟩ := density_eig hP
  rw [← traceRpow_two hH, traceRpow_eq hH]
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < hH.eigenvalues i := by
    by_contra h; push Not at h
    have : ∑ i, hH.eigenvalues i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (h0 i)
    linarith
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hi0 2)
    (Finset.single_le_sum (f := fun i => hH.eigenvalues i ^ (2:ℝ))
      (fun i _ => Real.rpow_nonneg (h0 i) 2) (Finset.mem_univ i0))

lemma log_prod_inv {N : ℕ} (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) :
    -Real.log (∏ j, ((d j : ℝ) - 1)⁻¹) = ∑ j, Real.log ((d j : ℝ) - 1) := by
  have hpos : ∀ j, 0 < (d j : ℝ) - 1 := by
    intro j; have : (2:ℝ) ≤ d j := by exact_mod_cast hd j
    linarith
  rw [Real.log_prod (fun j _ => (inv_pos.mpr (hpos j)).ne'), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro j _; rw [Real.log_inv, neg_neg]

lemma lower_bound {N : ℕ} (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (Ω : Config d → ℂ) (hΩ : IsUnitVector Ω) :
    ∑ j, Real.log ((d j : ℝ) - 1) ≤
      renyiEntropy p (tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω)) := by
  set X := tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω) with hXdef
  have hXd := tensor_density d hd Ω hΩ
  have h2 := (order_bounds_aux X hXd p hp1 hp2).1
  refine le_trans ?_ h2
  have hS2 : renyiEntropy 2 X = -Real.log ((X * X).trace.re) := by
    unfold renyiEntropy; rw [if_neg (by norm_num), traceRpow_two hXd.1.isHermitian]; norm_num; rfl
  rw [hS2, ← log_prod_inv d hd, neg_le_neg_iff]
  have hb := (eq8_aux N d hd Ω hΩ).2.2.2.2.2
  exact Real.log_le_log (trace_sq_pos hXd) hb

lemma wh_E00 (n : ℕ) (a : Fin n) :
    wernerHolevo n (Matrix.single a a 1) = ((n : ℂ) - 1)⁻¹ • (1 - Matrix.single a a 1) := by
  unfold wernerHolevo
  rw [Matrix.trace_single_eq_same, one_smul, Matrix.transpose_single]

lemma wh_E00_sq (n : ℕ) (a : Fin n) :
    wernerHolevo n (Matrix.single a a 1) * wernerHolevo n (Matrix.single a a 1) =
      ((n : ℂ) - 1)⁻¹ • wernerHolevo n (Matrix.single a a 1) := by
  rw [wh_E00, smul_mul_smul_comm, sub_mul, mul_sub, mul_sub, Matrix.single_mul_single_same,
    smul_smul]
  simp

lemma upper_value {N : ℕ} (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (p : ℝ) (hp1 : 1 ≤ p) :
    ∃ Ω : Config d → ℂ, IsUnitVector Ω ∧
      renyiEntropy p (tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω)) =
        ∑ j, Real.log ((d j : ℝ) - 1) := by
  let x0 : Config d := fun j => ⟨0, by have := hd j; omega⟩
  let Ω : Config d → ℂ := fun x => if x = x0 then 1 else 0
  have hΩ : IsUnitVector Ω := by
    unfold IsUnitVector
    rw [Finset.sum_eq_single x0]
    · simp [Ω]
    · intro b _ hb; simp [Ω, hb]
    · simp
  refine ⟨Ω, hΩ, ?_⟩
  set X := tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω) with hXdef
  have hXd := tensor_density d hd Ω hΩ
  have hentry : ∀ y y', X y y' = ∏ j, wernerHolevo (d j) (Matrix.single (x0 j) (x0 j) 1) (y j) (y' j) := by
    intro y y'
    rw [hXdef]
    simp only [tensorChannel, Matrix.of_apply, pureState, Matrix.vecMulVec_apply, Pi.star_apply]
    rw [sum2_single _ x0 x0]
    · simp [Ω]
    · intro a b h
      by_contra hc
      apply h
      by_cases ha : a = x0
      · have hb : b ≠ x0 := fun hb => hc ⟨ha, hb⟩
        simp [Ω, hb]
      · simp [Ω, ha]
  set c : ℝ := ∏ j, ((d j : ℝ) - 1)⁻¹ with hc
  have hcpos : 0 < c := by
    apply Finset.prod_pos; intro j _
    have : (2:ℝ) ≤ d j := by exact_mod_cast hd j
    apply inv_pos.mpr; linarith
  have hXX : X * X = (c : ℂ) • X := by
    ext y y''
    rw [Matrix.mul_apply, Matrix.smul_apply, hentry, smul_eq_mul]
    simp_rw [hentry, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun j (b : Fin (d j)) =>
      wernerHolevo (d j) (Matrix.single (x0 j) (x0 j) 1) (y j) b *
        wernerHolevo (d j) (Matrix.single (x0 j) (x0 j) 1) b (y'' j))]
    have : ∀ j, (∑ b : Fin (d j), wernerHolevo (d j) (Matrix.single (x0 j) (x0 j) 1) (y j) b *
        wernerHolevo (d j) (Matrix.single (x0 j) (x0 j) 1) b (y'' j)) =
        ((d j : ℂ) - 1)⁻¹ * wernerHolevo (d j) (Matrix.single (x0 j) (x0 j) 1) (y j) (y'' j) := by
      intro j
      rw [← Matrix.mul_apply, wh_E00_sq, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.prod_congr rfl (fun j _ => this j), Finset.prod_mul_distrib, hc]
    push_cast; rfl
  rw [renyi_of_idem hXd.1.isHermitian c hcpos hXX hXd.2 p hp1, hc, log_prod_inv d hd]

theorem solution (N : ℕ) (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (p : ℝ) (hp1 : 1 ≤ p)
    (hp2 : p ≤ 2) :
    BddBelow (outputEntropies p (tensorChannel d fun j => wernerHolevo (d j))) ∧
    (∀ j, BddBelow (outputEntropies p (wernerHolevo (d j)))) ∧
    minOutputEntropy p (tensorChannel d fun j => wernerHolevo (d j)) =
      ∑ j, minOutputEntropy p (wernerHolevo (d j)) := by
  have hleast : IsLeast (outputEntropies p (tensorChannel d fun j => wernerHolevo (d j)))
      (∑ j, Real.log ((d j : ℝ) - 1)) := by
    constructor
    · obtain ⟨Ω, hΩ, h⟩ := upper_value d hd p hp1
      exact ⟨Ω, hΩ, h.symm⟩
    · rintro s ⟨Ω, hΩ, rfl⟩
      exact lower_bound d hd p hp1 hp2 Ω hΩ
  refine ⟨hleast.bddBelow, fun j => ?_, ?_⟩
  · rw [outputEntropies_wh (d j) (hd j) p hp1]; exact bddBelow_singleton
  · unfold minOutputEntropy
    rw [hleast.csInf_eq]
    apply Finset.sum_congr rfl; intro j _
    rw [outputEntropies_wh (d j) (hd j) p hp1, csInf_singleton]

end helpers
