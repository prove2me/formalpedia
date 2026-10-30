-- Prove2me | solution 1 for PochetWolsey.Decomposition.tu_column_partition
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T06:34:30.070992+00:00
-- url     : https://prove2.me/submissions/28f647ed-3ec7-4da4-be24-65ce25cabe0f

import Mathlib

namespace TUGH

open Matrix

/-- core step: nonsingular integer matrix with ±1,0 adjugate and column-partition property has det ±1 -/
lemma core {k : ℕ} (B : Matrix (Fin (k+1)) (Fin (k+1)) ℤ)
    (hadj : ∀ i j, B.adjugate i j = 0 ∨ B.adjugate i j = 1 ∨ B.adjugate i j = -1)
    (hpart : ∀ J : Finset (Fin (k+1)), ∃ J₁ J₂ : Finset (Fin (k+1)),
      Disjoint J₁ J₂ ∧ J₁ ∪ J₂ = J ∧ ∀ i, |(∑ j ∈ J₁, B i j) - ∑ j ∈ J₂, B i j| ≤ 1)
    (hd : B.det ≠ 0) : B.det = 1 ∨ B.det = -1 := by
  classical
  set d := B.det with hd_def
  set v : Fin (k+1) → ℤ := fun i => B.adjugate i 0 with hv
  have hBv : ∀ i, (B *ᵥ v) i = if i = 0 then d else 0 := by
    intro i
    have h := congr_fun (congr_fun (Matrix.mul_adjugate B) i) 0
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
    simp only [Matrix.mulVec, dotProduct, hv]
    rw [h]
    by_cases hi : i = 0 <;> simp [hi, hd_def]
  set J0 : Finset (Fin (k+1)) := Finset.univ.filter (fun j => v j ≠ 0) with hJ0
  have hJne : ∃ j0, j0 ∈ J0 := by
    by_contra hcon
    push_neg at hcon
    have hv0 : v = 0 := by
      funext j
      by_contra hj
      have hj' : v j ≠ 0 := by simpa using hj
      exact hcon j (by simpa [hJ0] using hj')
    have := hBv 0
    rw [hv0] at this
    simp at this
    exact hd this.symm
  obtain ⟨j0, hj0⟩ := hJne
  obtain ⟨J₁, J₂, hdis, hun, hbd⟩ := hpart J0
  set z : Fin (k+1) → ℤ := fun j => (if j ∈ J₁ then 1 else 0) - (if j ∈ J₂ then 1 else 0) with hz
  have hmemJ : ∀ j, j ∈ J0 ↔ j ∈ J₁ ∨ j ∈ J₂ := by
    intro j; rw [← hun]; simp
  have hvJ : ∀ j, j ∈ J0 → v j = 1 ∨ v j = -1 := by
    intro j hj
    have hne : v j ≠ 0 := by simpa [hJ0] using hj
    rcases hadj j 0 with h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr h
  have hvn : ∀ j, j ∉ J0 → v j = 0 := by
    intro j hj; by_contra h; exact hj (by simp [hJ0, h])
  have hzJ : ∀ j, j ∈ J0 → z j = 1 ∨ z j = -1 := by
    intro j hj
    have hdj : ∀ j, j ∈ J₁ → j ∉ J₂ := fun j h1 h2 => Finset.disjoint_left.mp hdis h1 h2
    rcases (hmemJ j).1 hj with h1 | h2
    · left; simp [hz, h1, hdj j h1]
    · right
      have : j ∉ J₁ := fun h1 => hdj j h1 h2
      simp [hz, h2, this]
  have hzn : ∀ j, j ∉ J0 → z j = 0 := by
    intro j hj
    have h1 : j ∉ J₁ := fun h => hj ((hmemJ j).2 (Or.inl h))
    have h2 : j ∉ J₂ := fun h => hj ((hmemJ j).2 (Or.inr h))
    simp [hz, h1, h2]
  -- B z
  have hBz : ∀ i, (B *ᵥ z) i = (∑ j ∈ J₁, B i j) - ∑ j ∈ J₂, B i j := by
    intro i
    simp only [Matrix.mulVec, dotProduct, hz, mul_sub, mul_ite, mul_one, mul_zero,
      Finset.sum_sub_distrib]
    rw [Finset.sum_ite_mem, Finset.sum_ite_mem]
    simp
  have hw : ∀ i, |(B *ᵥ z) i| ≤ 1 := fun i => by rw [hBz]; exact hbd i
  -- evenness
  have hev : ∀ j, ∃ c : ℤ, z j - v j = 2 * c := by
    intro j
    by_cases hj : j ∈ J0
    · rcases hzJ j hj with h | h <;> rcases hvJ j hj with h' | h' <;>
        exact ⟨(z j - v j) / 2, by omega⟩
    · have h1 := hzn j hj
      have h2 := hvn j hj
      exact ⟨0, by omega⟩
  choose c hc using hev
  have hdiff : ∀ i, (B *ᵥ z) i - (if i = 0 then d else 0) = 2 * (B *ᵥ c) i := by
    intro i
    rw [← hBv i]
    have : z = v + (2:ℤ) • c := by
      funext j; have := hc j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; omega
    rw [this, Matrix.mulVec_add, Matrix.mulVec_smul]
    simp
  have hzero : ∀ i, i ≠ 0 → (B *ᵥ z) i = 0 := by
    intro i hi
    have h1 := hdiff i
    have h2 := hw i
    rw [if_neg hi] at h1
    rw [abs_le] at h2
    omega
  have hw0 : (B *ᵥ z) 0 = 0 ∨ (B *ᵥ z) 0 = 1 ∨ (B *ᵥ z) 0 = -1 := by
    have h2 := hw 0
    rw [abs_le] at h2
    omega
  rcases hw0 with h0 | h0 | h0
  · exfalso
    have hall : B *ᵥ z = 0 := by
      funext i
      by_cases hi : i = 0
      · subst hi; simpa using h0
      · simpa using hzero i hi
    have hz0 := Matrix.eq_zero_of_mulVec_eq_zero hd hall
    have := congr_fun hz0 j0
    rcases hzJ j0 hj0 with h | h <;> simp [h] at this
  · -- B z = e0
    have key : B *ᵥ (d • z - v) = 0 := by
      funext i
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hBv i, Pi.zero_apply]
      by_cases hi : i = 0
      · subst hi; rw [h0]; simp
      · rw [hzero i hi]; simp [hi]
    have hzv := Matrix.eq_zero_of_mulVec_eq_zero hd key
    have := congr_fun hzv j0
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rcases hzJ j0 hj0 with h | h <;> rcases hvJ j0 hj0 with h' | h' <;> rw [h, h'] at this <;> omega
  · have key : B *ᵥ (d • z + v) = 0 := by
      funext i
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hBv i, Pi.zero_apply]
      by_cases hi : i = 0
      · subst hi; rw [h0]; simp
      · rw [hzero i hi]; simp [hi]
    have hzv := Matrix.eq_zero_of_mulVec_eq_zero hd key
    have := congr_fun hzv j0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rcases hzJ j0 hj0 with h | h <;> rcases hvJ j0 hj0 with h' | h' <;> rw [h, h'] at this <;> omega


lemma part_sub {m n k : ℕ} (Z : Matrix (Fin m) (Fin n) ℤ)
    (hpart : ∀ J : Finset (Fin n), ∃ J₁ J₂ : Finset (Fin n),
      Disjoint J₁ J₂ ∧ J₁ ∪ J₂ = J ∧ ∀ i, |(∑ j ∈ J₁, Z i j) - ∑ j ∈ J₂, Z i j| ≤ 1)
    (f : Fin k → Fin m) (g : Fin k → Fin n) (hg : Function.Injective g) :
    ∀ J : Finset (Fin k), ∃ J₁ J₂ : Finset (Fin k),
      Disjoint J₁ J₂ ∧ J₁ ∪ J₂ = J ∧
      ∀ i, |(∑ j ∈ J₁, (Z.submatrix f g) i j) - ∑ j ∈ J₂, (Z.submatrix f g) i j| ≤ 1 := by
  classical
  intro J
  obtain ⟨K₁, K₂, hdis, hun, hbd⟩ := hpart (J.image g)
  have hmem : ∀ c, c ∈ K₁ ∨ c ∈ K₂ ↔ c ∈ J.image g := by
    intro c; rw [← hun]; simp
  have himg : ∀ K : Finset (Fin n), (∀ c ∈ K, c ∈ J.image g) →
      K = (J.filter (fun j => g j ∈ K)).image g := by
    intro K hK
    ext c
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · intro hc
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hK c hc)
      exact ⟨j, ⟨hj, hc⟩, rfl⟩
    · rintro ⟨j, ⟨_, hj⟩, rfl⟩; exact hj
  have h1 := himg K₁ (fun c hc => (hmem c).1 (Or.inl hc))
  have h2 := himg K₂ (fun c hc => (hmem c).1 (Or.inr hc))
  refine ⟨J.filter (fun j => g j ∈ K₁), J.filter (fun j => g j ∈ K₂), ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_filter] at hj1 hj2
    exact Finset.disjoint_left.mp hdis hj1.2 hj2.2
  · ext j
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hj
      have : g j ∈ J.image g := Finset.mem_image_of_mem g hj
      rcases (hmem _).2 this with h | h
      · exact Or.inl ⟨hj, h⟩
      · exact Or.inr ⟨hj, h⟩
  · intro i
    have := hbd (f i)
    rw [h1, h2, Finset.sum_image (fun a _ b _ h => hg h),
      Finset.sum_image (fun a _ b _ h => hg h)] at this
    simpa [Matrix.submatrix_apply] using this

lemma main_int {m n : ℕ} (Z : Matrix (Fin m) (Fin n) ℤ)
    (hpart : ∀ J : Finset (Fin n), ∃ J₁ J₂ : Finset (Fin n),
      Disjoint J₁ J₂ ∧ J₁ ∪ J₂ = J ∧ ∀ i, |(∑ j ∈ J₁, Z i j) - ∑ j ∈ J₂, Z i j| ≤ 1) :
    ∀ k (f : Fin k → Fin m) (g : Fin k → Fin n),
      (Z.submatrix f g).det = 0 ∨ (Z.submatrix f g).det = 1 ∨ (Z.submatrix f g).det = -1 := by
  intro k
  induction k with
  | zero => intro f g; right; left; simp
  | succ k ih =>
    intro f g
    by_cases hd : (Z.submatrix f g).det = 0
    · exact Or.inl hd
    · have hg : Function.Injective g := by
        intro a b hab
        by_contra hne
        apply hd
        apply Matrix.det_zero_of_column_eq hne
        intro i
        simp [Matrix.submatrix_apply, hab]
      have hadj : ∀ i j, (Z.submatrix f g).adjugate i j = 0 ∨ (Z.submatrix f g).adjugate i j = 1 ∨
          (Z.submatrix f g).adjugate i j = -1 := by
        intro i j
        rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.submatrix_submatrix]
        have h := ih (f ∘ j.succAbove) (g ∘ i.succAbove)
        rcases neg_one_pow_eq_or ℤ (j + i : ℕ) with hp | hp <;> rw [hp] <;> omega
      rcases core (Z.submatrix f g) hadj (part_sub Z hpart f g hg) hd with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

end TUGH

open TUGH in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hentries : ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1)
    (hpartition : ∀ J : Finset (Fin n), ∃ J₁ J₂ : Finset (Fin n),
      Disjoint J₁ J₂ ∧ J₁ ∪ J₂ = J ∧
      ∀ i, |(∑ j ∈ J₁, A i j) - ∑ j ∈ J₂, A i j| ≤ 1) :
    A.IsTotallyUnimodular := by
  classical
  let Z : Matrix (Fin m) (Fin n) ℤ := fun i j => if A i j = 1 then 1 else if A i j = -1 then -1 else 0
  have hZ : ∀ i j, A i j = (Z i j : ℝ) := by
    intro i j
    rcases hentries i j with h | h | h
    · have h1 : A i j ≠ 1 := by rw [h]; norm_num
      have h2 : A i j ≠ -1 := by rw [h]; norm_num
      simp [Z, h1, h2, h]
    · simp [Z, h]
    · have h1 : A i j ≠ 1 := by rw [h]; norm_num
      simp [Z, h1, h]
  have hA : A = Z.map (Int.castRingHom ℝ) := by
    ext i j; simp [hZ i j]
  have hpZ : ∀ J : Finset (Fin n), ∃ J₁ J₂ : Finset (Fin n),
      Disjoint J₁ J₂ ∧ J₁ ∪ J₂ = J ∧ ∀ i, |(∑ j ∈ J₁, Z i j) - ∑ j ∈ J₂, Z i j| ≤ 1 := by
    intro J
    obtain ⟨J₁, J₂, h1, h2, h3⟩ := hpartition J
    refine ⟨J₁, J₂, h1, h2, fun i => ?_⟩
    have := h3 i
    simp only [hZ] at this
    have e : ((∑ j ∈ J₁, Z i j - ∑ j ∈ J₂, Z i j : ℤ) : ℝ) = 0 + ((∑ j ∈ J₁, Z i j - ∑ j ∈ J₂, Z i j : ℤ) : ℝ) := by simp
    have h4 : |((∑ j ∈ J₁, Z i j - ∑ j ∈ J₂, Z i j : ℤ) : ℝ)| ≤ 1 := by
      push_cast; exact this
    exact_mod_cast h4
  rw [Matrix.isTotallyUnimodular_iff]
  intro k f g
  have hdet : (A.submatrix f g).det = (((Z.submatrix f g).det : ℤ) : ℝ) := by
    rw [hA]
    have := RingHom.map_det (Int.castRingHom ℝ) (Z.submatrix f g)
    simpa [Matrix.submatrix_map] using this.symm
  rw [hdet]
  rcases main_int Z hpZ k f g with h | h | h
  · exact ⟨0, by rw [h]; simp⟩
  · exact ⟨1, by rw [h]; simp⟩
  · exact ⟨-1, by rw [h]; simp⟩
