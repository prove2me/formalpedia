-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.proposition_2_12
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:10:18.119884+00:00
-- url     : https://prove2.me/submissions/a04272bf-c191-41c6-b657-5a0929973ec7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate BigOperators


namespace X6P26S

open QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

theorem outer_mul {d : ℕ} (u v : Fin d → ℂ) :
    (outer u u * outer v v : Matrix (Fin d) (Fin d) ℂ) = vectorInner u v • outer u v := by
  ext a b
  simp only [Matrix.mul_apply, outer, vectorInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => by ring

theorem trace_outer {d : ℕ} (u v : Fin d → ℂ) :
    (outer u v : Matrix (Fin d) (Fin d) ℂ).trace = vectorInner v u := by
  simp only [Matrix.trace, Matrix.diag, outer, vectorInner]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem conj_inner {d : ℕ} (u v : Fin d → ℂ) : conj (vectorInner u v) = vectorInner v u := by
  simp only [vectorInner, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem trace_outer_mul {d : ℕ} (u v : Fin d → ℂ) :
    (outer u u * outer v v : Matrix (Fin d) (Fin d) ℂ).trace =
      (Complex.normSq (vectorInner u v) : ℂ) := by
  rw [outer_mul, Matrix.trace_smul, trace_outer, smul_eq_mul, ← conj_inner u v,
    Complex.mul_conj]

theorem inner_self {d : ℕ} (u : Fin d → ℂ) :
    vectorInner u u = ((∑ k, Complex.normSq (u k) : ℝ) : ℂ) := by
  simp only [vectorInner, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, Complex.mul_conj]

/-- residual identity: for unit u and c = ⟨u,v⟩, ‖v - c u‖² = ‖v‖² - |c|². -/
theorem resid {d : ℕ} (u v : Fin d → ℂ) (hu : vectorInner u u = 1) :
    ∑ k, (v k - vectorInner u v * u k) * conj (v k - vectorInner u v * u k) =
      vectorInner v v - vectorInner u v * conj (vectorInner u v) := by
  set c := vectorInner u v with hc
  have h1 : ∑ k, u k * conj (v k) = conj c := by
    rw [hc, conj_inner]; simp only [vectorInner]; exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : ∑ k, v k * conj (u k) = c := by
    simp only [hc, vectorInner]; exact Finset.sum_congr rfl fun k _ => by ring
  have h3 : ∑ k, u k * conj (u k) = 1 := by
    rw [← hu]; simp only [vectorInner]; exact Finset.sum_congr rfl fun k _ => by ring
  have h4 : ∑ k, v k * conj (v k) = vectorInner v v := by
    simp only [vectorInner]; exact Finset.sum_congr rfl fun k _ => by ring
  have : ∀ k, (v k - c * u k) * conj (v k - c * u k) =
      v k * conj (v k) - c * (u k * conj (v k)) - conj c * (v k * conj (u k)) +
        (c * conj c) * (u k * conj (u k)) := by
    intro k; simp only [map_sub, map_mul]; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2, h3, h4]
  ring

theorem normSq_inner_le {d : ℕ} (u v : Fin d → ℂ) (hu : vectorInner u u = 1)
    (hv : vectorInner v v = 1) : Complex.normSq (vectorInner u v) ≤ 1 := by
  have h := resid u v hu
  rw [hv, Complex.mul_conj] at h
  have h' : ((∑ k, Complex.normSq (v k - vectorInner u v * u k) : ℝ) : ℂ) =
      ((1 - Complex.normSq (vectorInner u v) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Complex.ofReal_sub, Complex.ofReal_one, ← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj]
  have := Complex.ofReal_injective h'
  have : 0 ≤ ∑ k, Complex.normSq (v k - vectorInner u v * u k) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  linarith

theorem outer_eq_of {d : ℕ} (u v : Fin d → ℂ) (hu : vectorInner u u = 1)
    (hv : vectorInner v v = 1) (h : Complex.normSq (vectorInner u v) = 1) :
    outer v v = outer u u := by
  have hr := resid u v hu
  rw [hv, Complex.mul_conj, h] at hr
  have h0 : ∑ k, Complex.normSq (v k - vectorInner u v * u k) = 0 := by
    have : ((∑ k, Complex.normSq (v k - vectorInner u v * u k) : ℝ) : ℂ) = 0 := by
      have hr' : ∑ k, (v k - vectorInner u v * u k) * conj (v k - vectorInner u v * u k) = 0 := by
        rw [hr]; simp
      rw [Complex.ofReal_sum, ← hr']
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.mul_conj]
    exact_mod_cast this
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)] at h0
  have hv' : ∀ k, v k = vectorInner u v * u k := fun k =>
    sub_eq_zero.1 (Complex.normSq_eq_zero.1 (h0 k (Finset.mem_univ _)))
  have hc : vectorInner u v * conj (vectorInner u v) = 1 := by
    rw [Complex.mul_conj, h]; simp
  ext a b
  simp only [outer, hv', map_mul]
  calc vectorInner u v * u a * (conj (vectorInner u v) * conj (u b))
      = (vectorInner u v * conj (vectorInner u v)) * (u a * conj (u b)) := by ring
    _ = u a * conj (u b) := by rw [hc, one_mul]

section core
variable {d : ℕ} {ι : Type*} [Fintype ι] (c : ι → ℝ) (x y : ι → Fin d → ℂ)

def JJ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∑ i, (c i : ℂ) • Matrix.kronecker (outer (x i) (x i)) (outer (y i) (y i))

theorem ptr2_JJ (hy : ∀ i, vectorInner (y i) (y i) = 1) :
    (fun a b => ∑ k, JJ c x y (a, k) (b, k) : Matrix (Fin d) (Fin d) ℂ) =
      ∑ i, (c i : ℂ) • outer (x i) (x i) := by
  ext a b
  simp only [JJ, Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hy i
  simp only [vectorInner] at this
  simp only [outer]
  calc ∑ k, (c i : ℂ) * (x i a * conj (x i b) * (y i k * conj (y i k)))
      = (c i : ℂ) * (x i a * conj (x i b)) * ∑ k, conj (y i k) * y i k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by rw [this, mul_one]

theorem ptr1_JJ (hx : ∀ i, vectorInner (x i) (x i) = 1) :
    QAlgorithms.traceLeft (JJ c x y) = ∑ i, (c i : ℂ) • outer (y i) (y i) := by
  ext a b
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, JJ, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.kronecker_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hx i
  simp only [vectorInner] at this
  simp only [outer]
  calc ∑ k, (c i : ℂ) * (x i k * conj (x i k) * (y i a * conj (y i b)))
      = (c i : ℂ) * (y i a * conj (y i b)) * ∑ k, conj (x i k) * x i k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by rw [this, mul_one]

theorem trace_sum_outer (z : ι → Fin d → ℂ) (hz : ∀ i, vectorInner (z i) (z i) = 1) :
    (∑ i, (c i : ℂ) • outer (z i) (z i)).trace = ((∑ i, c i : ℝ) : ℂ) := by
  simp [Matrix.trace_sum, Matrix.trace_smul, trace_outer, hz]

theorem trace_sq_outer (z : ι → Fin d → ℂ) :
    ((∑ i, (c i : ℂ) • outer (z i) (z i)) * (∑ i, (c i : ℂ) • outer (z i) (z i))).trace =
      ((∑ i, ∑ j, c i * c j * Complex.normSq (vectorInner (z i) (z j)) : ℝ) : ℂ) := by
  rw [Finset.sum_mul_sum, Matrix.trace_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, Matrix.trace_smul, trace_outer_mul, smul_eq_mul]

theorem trace_JJ (hx : ∀ i, vectorInner (x i) (x i) = 1) (hy : ∀ i, vectorInner (y i) (y i) = 1) :
    (JJ c x y).trace = ((∑ i, c i : ℝ) : ℂ) := by
  simp [JJ, Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_kronecker, trace_outer, hx, hy]

theorem trace_JJ_sq :
    (JJ c x y * JJ c x y).trace = ((∑ i, ∑ j, c i * c j * Complex.normSq (vectorInner (x i) (x j)) *
      Complex.normSq (vectorInner (y i) (y j)) : ℝ) : ℂ) := by
  unfold JJ
  rw [Finset.sum_mul_sum, Matrix.trace_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have kk : ∀ A B C D : Matrix (Fin d) (Fin d) ℂ, Matrix.kronecker A B * Matrix.kronecker C D =
      Matrix.kronecker (A * C) (B * D) := fun A B C D => (Matrix.mul_kronecker_mul A C B D).symm
  rw [smul_mul_smul_comm, kk, Matrix.trace_smul]
  erw [Matrix.trace_kronecker]
  rw [
    trace_outer_mul, trace_outer_mul, smul_eq_mul]
  ring

theorem dichotomy (hc : ∀ i, 0 ≤ c i)
    (hx : ∀ i, vectorInner (x i) (x i) = 1) (hy : ∀ i, vectorInner (y i) (y i) = 1)
    (hJ : JJ c x y * JJ c x y = JJ c x y)
    (hM : (fun a b => ∑ k, JJ c x y (a, k) (b, k)) = (1 : Mat d))
    (hN : QAlgorithms.traceLeft (JJ c x y) = 1) (i j : ι) (hi : 0 < c i) (hj : 0 < c j) :
    (vectorInner (x i) (x j) = 0 ∧ vectorInner (y i) (y j) = 0) ∨
      (Complex.normSq (vectorInner (x i) (x j)) = 1 ∧
        Complex.normSq (vectorInner (y i) (y j)) = 1) := by
  set a := fun i j => Complex.normSq (vectorInner (x i) (x j))
  set b := fun i j => Complex.normSq (vectorInner (y i) (y j))
  have hsum : ∑ i, ∑ j, c i * c j * a i j * b i j = ∑ i, c i := by
    have := trace_JJ_sq c x y
    rw [hJ, trace_JJ c x y hx hy] at this
    exact (Complex.ofReal_injective this).symm
  have hMs : ∑ i, ∑ j, c i * c j * a i j = ∑ i, c i := by
    have h1 := trace_sq_outer c x
    have h2 := trace_sum_outer c x hx
    have e : ∑ i, (c i : ℂ) • outer (x i) (x i) = 1 := by rw [← ptr2_JJ c x y hy]; exact hM
    have h3 : ((∑ i, (c i : ℂ) • outer (x i) (x i)) * (∑ i, (c i : ℂ) • outer (x i) (x i))).trace =
        (∑ i, (c i : ℂ) • outer (x i) (x i)).trace := by rw [e]; simp
    rw [h1, h2] at h3
    exact Complex.ofReal_injective h3
  have hNs : ∑ i, ∑ j, c i * c j * b i j = ∑ i, c i := by
    have h1 := trace_sq_outer c y
    have h2 := trace_sum_outer c y hy
    have e : ∑ i, (c i : ℂ) • outer (y i) (y i) = 1 := by rw [← ptr1_JJ c x y hx]; exact hN
    have h3 : ((∑ i, (c i : ℂ) • outer (y i) (y i)) * (∑ i, (c i : ℂ) • outer (y i) (y i))).trace =
        (∑ i, (c i : ℂ) • outer (y i) (y i)).trace := by rw [e]; simp
    rw [h1, h2] at h3
    exact Complex.ofReal_injective h3
  have ha1 : ∀ i j, a i j ≤ 1 := fun i j => normSq_inner_le _ _ (hx i) (hx j)
  have hb1 : ∀ i j, b i j ≤ 1 := fun i j => normSq_inner_le _ _ (hy i) (hy j)
  have ha0 : ∀ i j, 0 ≤ a i j := fun i j => Complex.normSq_nonneg _
  have hb0 : ∀ i j, 0 ≤ b i j := fun i j => Complex.normSq_nonneg _
  have zero_of : ∀ f : ι → ι → ℝ, (∀ i j, 0 ≤ f i j) → ∑ i, ∑ j, f i j = 0 → f i j = 0 := by
    intro f hf h
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hf i j)] at h
    have := h i (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hf i j)] at this
    exact this j (Finset.mem_univ _)
  have e1 := zero_of (fun i j => c i * c j * a i j * (1 - b i j))
    (fun i j => mul_nonneg (mul_nonneg (mul_nonneg (hc i) (hc j)) (ha0 i j))
      (by linarith [hb1 i j]))
    (by simp only [mul_sub, mul_one, Finset.sum_sub_distrib]; linarith)
  have e2 := zero_of (fun i j => c i * c j * b i j * (1 - a i j))
    (fun i j => mul_nonneg (mul_nonneg (mul_nonneg (hc i) (hc j)) (hb0 i j))
      (by linarith [ha1 i j]))
    (by simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
        have : ∑ i, ∑ j, c i * c j * b i j * a i j = ∑ i, ∑ j, c i * c j * a i j * b i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        linarith)
  have hcc : 0 < c i * c j := mul_pos hi hj
  have e1' : a i j * (1 - b i j) = 0 := by
    have : c i * c j * (a i j * (1 - b i j)) = 0 := by rw [← e1]; ring
    exact (mul_eq_zero.1 this).resolve_left hcc.ne'
  have e2' : b i j * (1 - a i j) = 0 := by
    have : c i * c j * (b i j * (1 - a i j)) = 0 := by rw [← e2]; ring
    exact (mul_eq_zero.1 this).resolve_left hcc.ne'
  rcases mul_eq_zero.1 e1' with h | h
  · left
    have hb : b i j = 0 := by
      rw [h] at e2'; simpa using e2'
    exact ⟨Complex.normSq_eq_zero.1 h, Complex.normSq_eq_zero.1 hb⟩
  · right
    have hb : b i j = 1 := by linarith
    rw [hb] at e2'
    exact ⟨by linarith, hb⟩

theorem structure_thm (hc : ∀ i, 0 ≤ c i)
    (hx : ∀ i, vectorInner (x i) (x i) = 1) (hy : ∀ i, vectorInner (y i) (y i) = 1)
    (hJ : JJ c x y * JJ c x y = JJ c x y)
    (hM : (fun a b => ∑ k, JJ c x y (a, k) (b, k)) = (1 : Mat d))
    (hN : QAlgorithms.traceLeft (JJ c x y) = 1) :
    ∃ U V : Unitary d, JJ c x y = ∑ k : Fin d,
      Matrix.kronecker (outer (fun i => (U : Mat d) i k) (fun i => (U : Mat d) i k))
        (outer (fun i => (V : Mat d) i k) (fun i => (V : Mat d) i k)) := by
  let X : ι → Mat d := fun i => outer (x i) (x i)
  let Y : ι → Mat d := fun i => outer (y i) (y i)
  let G := Finset.univ.filter (fun i => 0 < c i)
  let S := G.image X
  have hG : ∀ i, i ∉ G → c i = 0 := by
    intro i hi; simp [G] at hi; linarith [hc i]
  have hD := dichotomy c x y hc hx hy hJ hM hN
  have hxx : ∀ i, Complex.normSq (vectorInner (x i) (x i)) = 1 := fun i => by rw [hx i]; simp
  -- same projector ⇒ parallel in both factors
  have same : ∀ i ∈ G, ∀ j ∈ G, X i = X j →
      Complex.normSq (vectorInner (x i) (x j)) = 1 ∧ Y j = Y i := by
    intro i hi j hj hij
    have hi' : 0 < c i := (Finset.mem_filter.1 hi).2
    have hj' : 0 < c j := (Finset.mem_filter.1 hj).2
    rcases hD i j hi' hj' with h | h
    · exfalso
      have h1 := trace_outer_mul (x i) (x j)
      have h2 := trace_outer_mul (x i) (x i)
      rw [h.1] at h1
      change (X i * X j).trace = _ at h1
      change (X i * X i).trace = _ at h2
      rw [← hij, h2, hxx] at h1
      simp at h1
    · exact ⟨h.1, outer_eq_of _ _ (hy i) (hy j) h.2⟩
  have diff : ∀ i ∈ G, ∀ j ∈ G, X i ≠ X j →
      vectorInner (x i) (x j) = 0 ∧ vectorInner (y i) (y j) = 0 := by
    intro i hi j hj hij
    rcases hD i j (Finset.mem_filter.1 hi).2 (Finset.mem_filter.1 hj).2 with h | h
    · exact h
    · exact absurd (outer_eq_of _ _ (hx i) (hx j) h.1).symm hij
  -- representatives
  have hrep : ∀ P : S, ∃ i, i ∈ G ∧ X i = P.1 := fun P => by
    have := Finset.mem_image.1 P.2; exact this
  let r : S → ι := fun P => Classical.choose (hrep P)
  have r_mem : ∀ P, r P ∈ G := fun P => (Classical.choose_spec (hrep P)).1
  have r_spec : ∀ P, X (r P) = P.1 := fun P => (Classical.choose_spec (hrep P)).2
  -- fiber weights
  have maps : ∀ i ∈ G, X i ∈ S := fun i hi => Finset.mem_image_of_mem X hi
  have wt : ∀ P : S, ∑ i ∈ G.filter (fun i => X i = P.1), c i = 1 := by
    intro P
    have e1 : ((∑ i, (c i : ℂ) • X i) * X (r P)).trace = 1 := by
      have : ∑ i, (c i : ℂ) • X i = 1 := by rw [← ptr2_JJ c x y hy]; exact hM
      rw [this, Matrix.one_mul]
      change (outer (x (r P)) (x (r P))).trace = 1
      rw [trace_outer, hx]
    rw [Finset.sum_mul, Matrix.trace_sum] at e1
    have e2 : ∀ i, ((c i : ℂ) • X i * X (r P)).trace =
        ((if i ∈ G.filter (fun i => X i = P.1) then c i else 0 : ℝ) : ℂ) := by
      intro i
      rw [Matrix.smul_mul, Matrix.trace_smul, trace_outer_mul, smul_eq_mul]
      by_cases hi : i ∈ G
      · by_cases hX : X i = P.1
        · rw [if_pos (show i ∈ G.filter (fun i => X i = P.1) from Finset.mem_filter.2 ⟨hi, hX⟩),
            (same i hi (r P) (r_mem P) (hX.trans (r_spec P).symm)).1]
          simp
        · rw [if_neg (show i ∉ G.filter (fun i => X i = P.1) from
              fun h => hX (Finset.mem_filter.1 h).2),
            (diff i hi (r P) (r_mem P) (fun h => hX (h.trans (r_spec P)))).1]
          simp
      · rw [hG i hi]; simp
    simp only [e2] at e1
    rw [← Complex.ofReal_sum] at e1
    have := Complex.ofReal_injective (e1.trans Complex.ofReal_one.symm)
    rwa [Finset.sum_ite_mem, Finset.univ_inter] at this
  have hsumG : ∑ i, c i = ∑ i ∈ G, c i := by
    rw [← Finset.sum_subset (Finset.subset_univ G) (fun i _ hi => hG i hi)]
  have hfib : ∑ i ∈ G, c i = S.card := by
    rw [← Finset.sum_fiberwise_of_maps_to maps, ← Finset.sum_coe_sort S]
    have : ∀ P : S, ∑ i ∈ G with X i = P.1, c i = 1 := wt
    simp [this]
  have hd : ∑ i, c i = d := by
    have h1 := trace_sum_outer c x hx
    have : ∑ i, (c i : ℂ) • outer (x i) (x i) = 1 := by rw [← ptr2_JJ c x y hy]; exact hM
    rw [this, Matrix.trace_one] at h1
    simp at h1
    exact_mod_cast h1.symm
  have hcard : Fintype.card S = d := by
    rw [Fintype.card_coe]
    have := hsumG.symm.trans hd
    rw [hfib] at this
    exact_mod_cast this
  let e : Fin d ≃ S := (Fintype.equivFinOfCardEq hcard).symm
  have orth : ∀ k l : Fin d, k ≠ l →
      vectorInner (x (r (e k))) (x (r (e l))) = 0 ∧ vectorInner (y (r (e k))) (y (r (e l))) = 0 := by
    intro k l hkl
    refine diff _ (r_mem _) _ (r_mem _) ?_
    rw [r_spec, r_spec]
    intro h
    exact hkl (e.injective (Subtype.ext h))
  let Um : Mat d := Matrix.of fun a k => x (r (e k)) a
  let Vm : Mat d := Matrix.of fun a k => y (r (e k)) a
  have unit_of : ∀ (z : ι → Fin d → ℂ), (∀ i, vectorInner (z i) (z i) = 1) →
      (∀ k l : Fin d, k ≠ l → vectorInner (z (r (e k))) (z (r (e l))) = 0) →
      (Matrix.of fun a k => z (r (e k)) a : Mat d) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    intro z hz hzo
    rw [Matrix.mem_unitaryGroup_iff']
    ext k l
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
    change vectorInner (z (r (e k))) (z (r (e l))) = _
    split_ifs with hkl
    · rw [hkl, hz]
    · exact hzo k l hkl
  refine ⟨⟨Um, unit_of x hx fun k l h => (orth k l h).1⟩,
    ⟨Vm, unit_of y hy fun k l h => (orth k l h).2⟩, ?_⟩
  change JJ c x y = ∑ k : Fin d, Matrix.kronecker (X (r (e k))) (Y (r (e k)))
  rw [Equiv.sum_comp e (fun P => Matrix.kronecker (X (r P)) (Y (r P)))]
  unfold JJ
  change ∑ i, (c i : ℂ) • Matrix.kronecker (X i) (Y i) = _
  rw [← Finset.sum_subset (Finset.subset_univ G) (fun i _ hi => by simp [hG i hi]),
    ← Finset.sum_fiberwise_of_maps_to maps, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun P _ => ?_
  have : ∀ i ∈ G.filter (fun i => X i = P.1),
      (c i : ℂ) • Matrix.kronecker (X i) (Y i) =
        (c i : ℂ) • Matrix.kronecker (X (r P)) (Y (r P)) := by
    intro i hi
    have hi' := Finset.mem_filter.1 hi
    have hXr : X i = X (r P) := hi'.2.trans (r_spec P).symm
    rw [hXr, ← (same i hi'.1 (r P) (r_mem P) hXr).2]
  rw [Finset.sum_congr rfl this, ← Finset.sum_smul]
  have := wt P
  rw [← Complex.ofReal_sum, this, Complex.ofReal_one, one_smul]

end core

end X6P26S

open scoped Matrix ComplexOrder ComplexConjugate BigOperators

namespace X6P26C

open QAlgorithms.Papers.Independent.Information100.P26

theorem adD {d : ℕ} (U : Mat d) (p r : Fin d × Fin d) :
    (ad U * dephasing d) p r = if r.1 = r.2 then ad U p r else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · simp only [dephasing, and_true]; split_ifs <;> simp
  · intro b _ hb; simp only [dephasing]; split_ifs with h
    · exact absurd h.2 hb
    · simp
  · simp

theorem sum_diag {d : ℕ} (f : Fin d × Fin d → ℂ) :
    ∑ r : Fin d × Fin d, (if r.1 = r.2 then f r else 0) = ∑ k, f (k, k) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k] <;> simp +contextual [eq_comm]

theorem beta_apply {d : ℕ} (U V : Unitary d) (p q : Fin d × Fin d) :
    beta U V p q = ∑ k, (U : Mat d) p.1 k * conj ((U : Mat d) p.2 k) *
      (conj ((V : Mat d) q.1 k) * (V : Mat d) q.2 k) := by
  unfold beta
  rw [Matrix.mul_apply]
  simp only [adD, ite_mul, zero_mul]
  rw [sum_diag]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ad, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]

theorem herm_expand {d : ℕ} {H : Mat d} (hH : H.IsHermitian) (a b : Fin d) :
    H a b = ∑ i, (hH.eigenvectorUnitary : Mat d) a i * (hH.eigenvalues i : ℂ) *
      conj ((hH.eigenvectorUnitary : Mat d) b i) := by
  conv_lhs => rw [hH.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.star_apply, Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, RCLike.star_def]
  rfl

end X6P26C

open scoped Matrix ComplexOrder ComplexConjugate BigOperators


namespace X6P26Q

open QAlgorithms.Papers.Independent.Information100.P26 X6P26S X6P26C

attribute [local instance] Classical.propDecidable Classical.decEq

def col {d : ℕ} (U : Unitary d) (k : Fin d) : Fin d → ℂ := fun i => (U : Mat d) i k

theorem col_inner {d : ℕ} (U : Unitary d) (k l : Fin d) :
    vectorInner (col U k) (col U l) = if k = l then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 U.2) k) l
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]; rfl

theorem rows_sum {d : ℕ} (U : Unitary d) (a b : Fin d) :
    ∑ k, col U k a * conj (col U k b) = if a = b then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 U.2) a) b
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]; rfl

def conjU {d : ℕ} (V : Unitary d) : Unitary d :=
  ⟨Matrix.of fun i j => conj ((V : Mat d) i j), by
    rw [Matrix.mem_unitaryGroup_iff']
    ext k l
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 V.2) k) l
    rw [Matrix.mul_apply, Matrix.one_apply] at h ⊢
    calc _ = conj (∑ j, star (V : Mat d) k j * (V : Mat d) j l) := by
          simp [Matrix.star_apply, map_sum]
      _ = _ := by rw [h]; split_ifs <;> simp⟩

theorem conjU_conjU {d : ℕ} (V : Unitary d) : conjU (conjU V) = V := by
  apply Subtype.ext; ext i j; simp [conjU]

theorem choi_choi {d : ℕ} (t : Map d) : choi (choi t) = t := by ext p q; rfl

theorem choi_beta {d : ℕ} (U V : Unitary d) :
    choi (beta U V) = ∑ k : Fin d, Matrix.kronecker
      (outer (fun i => (U : Mat d) i k) (fun i => (U : Mat d) i k))
      (outer (fun i => (conjU V : Mat d) i k) (fun i => (conjU V : Mat d) i k)) := by
  ext p q
  simp only [choi, beta_apply, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    outer, conjU, Matrix.of_apply, Complex.conj_conj]

theorem part1 {d : ℕ} (t : Map d) :
    Twisted t ↔ ∃ U V : Unitary d,
      choi t = ∑ k : Fin d,
        Matrix.kronecker
          (outer (fun i => (U : Mat d) i k) (fun i => (U : Mat d) i k))
          (outer (fun i => (V : Mat d) i k) (fun i => (V : Mat d) i k)) := by
  constructor
  · rintro ⟨U, V, rfl⟩
    exact ⟨U, conjU V, choi_beta U V⟩
  · rintro ⟨U, V, h⟩
    refine ⟨U, conjU V, ?_⟩
    have := choi_beta U (conjU V)
    rw [conjU_conjU] at this
    rw [← choi_choi t, h, ← this, choi_choi]

theorem JJ_one {d : ℕ} (U W : Unitary d) :
    JJ (fun _ : Fin d => (1 : ℝ)) (col U) (col W) = ∑ k : Fin d, Matrix.kronecker
      (outer (fun i => (U : Mat d) i k) (fun i => (U : Mat d) i k))
      (outer (fun i => (W : Mat d) i k) (fun i => (W : Mat d) i k)) := by
  simp [JJ]; rfl

theorem sum_outer_col {d : ℕ} (U : Unitary d) :
    ∑ i : Fin d, (((fun _ : Fin d => (1 : ℝ)) i : ℝ) : ℂ) • outer (col U i) (col U i) = (1 : Mat d) := by
  ext a b
  simp only [Complex.ofReal_one, one_smul, Matrix.sum_apply, outer]
  rw [rows_sum, Matrix.one_apply]

theorem outer_psd {d : ℕ} (u : Fin d → ℂ) : (outer u u : Mat d).PosSemidef := by
  have : (outer u u : Mat d) = Matrix.vecMulVec u (star u) := by
    ext a b; simp [outer, Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star u

theorem forward2 {d : ℕ} (U W : Unitary d) (J : Map d)
    (hJ : J = ∑ k : Fin d, Matrix.kronecker
      (outer (fun i => (U : Mat d) i k) (fun i => (U : Mat d) i k))
      (outer (fun i => (W : Mat d) i k) (fun i => (W : Mat d) i k))) :
    QAlgorithms.Entanglement.IsSeparablePositive J ∧
      Jᴴ = J ∧ J * J = J ∧
      (fun i j => ∑ k, J (i,k) (j,k)) = (1 : Mat d) ∧
      QAlgorithms.traceLeft J = (1 : Mat d) := by
  rw [← JJ_one] at hJ
  subst hJ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨d, fun _ => 1, fun k => outer (col U k) (col U k), fun k => outer (col W k) (col W k),
      fun _ => zero_le_one, fun k => ⟨⟨outer_psd _, ?_⟩, ⟨outer_psd _, ?_⟩⟩, ?_⟩
    · rw [trace_outer, col_inner, if_pos rfl]
    · rw [trace_outer, col_inner, if_pos rfl]
    · simp [JJ]
  · ext p q
    simp only [JJ, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, outer, star_sum, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.star_def, map_mul, Complex.conj_conj, Complex.conj_ofReal]; ring
  · unfold JJ
    rw [Finset.sum_mul_sum]
    have kk : ∀ A B C D : Matrix (Fin d) (Fin d) ℂ, Matrix.kronecker A B * Matrix.kronecker C D =
        Matrix.kronecker (A * C) (B * D) := fun A B C D => (Matrix.mul_kronecker_mul A C B D).symm
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_mul_smul_comm, kk, outer_mul, col_inner]
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl; simp [Ne.symm hl]
    · simp
  · rw [ptr2_JJ _ _ _ (fun i => by rw [col_inner, if_pos rfl]), sum_outer_col]
  · rw [ptr1_JJ _ _ _ (fun i => by rw [col_inner, if_pos rfl]), sum_outer_col]

theorem herm_expand' {d : ℕ} {H : Mat d} (hH : H.IsHermitian) (a b : Fin d) :
    H a b = ∑ i, (hH.eigenvalues i : ℂ) * (col hH.eigenvectorUnitary i a *
      conj (col hH.eigenvectorUnitary i b)) := by
  rw [herm_expand hH a b]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [col]; ring

theorem backward2 {d : ℕ} (J : Map d) (hsep : QAlgorithms.Entanglement.IsSeparablePositive J)
    (hP : J * J = J) (hM : (fun i j => ∑ k, J (i,k) (j,k)) = (1 : Mat d))
    (hN : QAlgorithms.traceLeft J = (1 : Mat d)) :
    ∃ U V : Unitary d, J = ∑ k : Fin d, Matrix.kronecker
      (outer (fun i => (U : Mat d) i k) (fun i => (U : Mat d) i k))
      (outer (fun i => (V : Mat d) i k) (fun i => (V : Mat d) i k)) := by
  obtain ⟨q, w, A, B, hw, hAB, hJ⟩ := hsep
  have hA : ∀ j, (A j).IsHermitian := fun j => (hAB j).1.1.1
  have hB : ∀ j, (B j).IsHermitian := fun j => (hAB j).2.1.1
  let c : Fin q × Fin d × Fin d → ℝ := fun z =>
    w z.1 * (hA z.1).eigenvalues z.2.1 * (hB z.1).eigenvalues z.2.2
  let x : Fin q × Fin d × Fin d → Fin d → ℂ := fun z => col (hA z.1).eigenvectorUnitary z.2.1
  let y : Fin q × Fin d × Fin d → Fin d → ℂ := fun z => col (hB z.1).eigenvectorUnitary z.2.2
  have hc : ∀ z, 0 ≤ c z := fun z =>
    mul_nonneg (mul_nonneg (hw z.1) ((hAB z.1).1.1.eigenvalues_nonneg _))
      ((hAB z.1).2.1.eigenvalues_nonneg _)
  have hx : ∀ z, vectorInner (x z) (x z) = 1 := fun z => by simp [x, col_inner]
  have hy : ∀ z, vectorInner (y z) (y z) = 1 := fun z => by simp [y, col_inner]
  have hJJ : J = JJ c x y := by
    rw [hJ]
    ext p p'
    simp only [JJ, Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, smul_eq_mul, outer]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type, herm_expand' (hA j), herm_expand' (hB j), Finset.sum_mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [c, x, y]; push_cast; ring
  rw [hJJ] at hP hM hN ⊢
  exact structure_thm c x y hc hx hy hP hM hN

end X6P26Q


open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 0 < d) (t : Map d) :
    (Twisted t ↔ ∃ U V : Unitary d,
      choi t = ∑ k : Fin d,
        Matrix.kronecker
          (outer (fun i => U i k) (fun i => U i k))
          (outer (fun i => V i k) (fun i => V i k))) ∧
    (Twisted t ↔ QAlgorithms.Entanglement.IsSeparablePositive (choi t) ∧
      (choi t)ᴴ = choi t ∧ choi t * choi t = choi t ∧
      (fun i j => ∑ k, choi t (i,k) (j,k)) = (1 : Mat d) ∧
      QAlgorithms.traceLeft (choi t) = (1 : Mat d)) := by
  refine ⟨X6P26Q.part1 t, ?_⟩
  rw [X6P26Q.part1 t]
  constructor
  · rintro ⟨U, V, h⟩
    exact X6P26Q.forward2 U V _ h
  · rintro ⟨h1, -, h3, h4, h5⟩
    exact X6P26Q.backward2 _ h1 h3 h4 h5

end
