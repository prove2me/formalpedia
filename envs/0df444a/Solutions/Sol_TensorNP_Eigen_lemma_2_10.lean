-- Prove2me | solution 1 for TensorNP.Eigen.lemma_2_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:40:46.288001+00:00
-- url     : https://prove2.me/submissions/0f49980f-32aa-48c5-96be-44e940d7699c

import Mathlib
import Definitions.Def_TensorNP_Bilinear_ColorEncoding
import Definitions.Def_TensorNP_Eigen_Construction

open Matrix Finset

private lemma dotProduct_single_one_mulVec {n : ℕ} (a b : Fin n) (p : Fin n → ℂ) :
    p ⬝ᵥ (Matrix.single a b (1 : ℂ) *ᵥ p) = p a * p b := by
  simp [dotProduct, Matrix.mulVec, Matrix.single]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hj; simp [hj.symm]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  · intro i _ hi; simp [hi.symm]
  · intro ha; exact absurd (Finset.mem_univ a) ha

private lemma map_sub_ratCast {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    (A - B).map (Rat.cast : ℚ → ℂ) = A.map (Rat.cast : ℚ → ℂ) - B.map (Rat.cast : ℚ → ℂ) := by
  ext i j; simp

private lemma map_add_ratCast {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    (A + B).map (Rat.cast : ℚ → ℂ) = A.map (Rat.cast : ℚ → ℂ) + B.map (Rat.cast : ℚ → ℂ) := by
  ext i j; simp

private lemma map_sum_ratCast {v n : ℕ} (s : Finset (Fin v)) (f : Fin v → Matrix (Fin n) (Fin n) ℚ) :
    (∑ j ∈ s, f j).map (Rat.cast : ℚ → ℂ) = ∑ j ∈ s, (f j).map (Rat.cast : ℚ → ℂ) := by
  ext a b; simp [Matrix.sum_apply, Rat.cast_sum]

private lemma map_single_one_ratCast {n : ℕ} (a b : Fin n) :
    (Matrix.single a b (1 : ℚ)).map (Rat.cast : ℚ → ℂ) = Matrix.single a b (1 : ℂ) := by
  ext i j; simp [Matrix.single]; split_ifs <;> simp

private lemma eigen_quad_eq_bilin {v : ℕ} (G : SimpleGraph (Fin v)) (c : Fin 4) (i : Fin v)
    (p : Fin (2 * v + 1) → ℂ) :
    p ⬝ᵥ (TensorNP.Eigen.castMatrices ℂ (TensorNP.Eigen.colorEncoding G) (c, i) *ᵥ p) =
      TensorNP.Bilinear.colorEncoding G c i p := by
  classical
  rcases c with ⟨c_val, hc⟩
  interval_cases c_val
  · simp only [TensorNP.Eigen.castMatrices, TensorNP.Eigen.colorEncoding,
      TensorNP.Bilinear.colorEncoding, Fin.zero_eta, Matrix.cons_val_zero,
      map_sub_ratCast, map_single_one_ratCast, Matrix.sub_mulVec, dotProduct_sub,
      dotProduct_single_one_mulVec, sq, TensorNP.Eigen.xVar, TensorNP.Eigen.yVar,
      TensorNP.Eigen.zVar, TensorNP.Bilinear.xIdx, TensorNP.Bilinear.yIdx, TensorNP.Bilinear.zIdx]
  · simp only [TensorNP.Eigen.castMatrices, TensorNP.Eigen.colorEncoding,
      TensorNP.Bilinear.colorEncoding, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      map_sub_ratCast, map_single_one_ratCast, Matrix.sub_mulVec, dotProduct_sub,
      dotProduct_single_one_mulVec, sq, TensorNP.Eigen.xVar, TensorNP.Eigen.yVar,
      TensorNP.Eigen.zVar, TensorNP.Bilinear.xIdx, TensorNP.Bilinear.yIdx, TensorNP.Bilinear.zIdx]
  · have hc2 : TensorNP.Eigen.colorEncoding G (⟨2, hc⟩, i) =
        single (TensorNP.Eigen.xVar i) TensorNP.Eigen.zVar 1 -
          single (TensorNP.Eigen.yVar i) (TensorNP.Eigen.yVar i) 1 := rfl
    simp only [TensorNP.Eigen.castMatrices, hc2, TensorNP.Bilinear.colorEncoding,
      map_sub_ratCast, map_single_one_ratCast, Matrix.sub_mulVec, dotProduct_sub,
      dotProduct_single_one_mulVec, sq, TensorNP.Eigen.xVar, TensorNP.Eigen.yVar,
      TensorNP.Eigen.zVar, TensorNP.Bilinear.xIdx, TensorNP.Bilinear.yIdx, TensorNP.Bilinear.zIdx]
  · have hc3 : TensorNP.Eigen.colorEncoding G (⟨3, hc⟩, i) =
        ∑ j ∈ univ.filter (G.Adj i),
          (single (TensorNP.Eigen.xVar i) (TensorNP.Eigen.xVar i) 1 +
            single (TensorNP.Eigen.xVar i) (TensorNP.Eigen.xVar j) 1 +
            single (TensorNP.Eigen.xVar j) (TensorNP.Eigen.xVar j) 1) := rfl
    simp only [TensorNP.Eigen.castMatrices, hc3, TensorNP.Bilinear.colorEncoding, map_sum_ratCast]
    have hsum : ∀ (s : Finset (Fin v)) (f : Fin v → Matrix (Fin (2 * v + 1)) (Fin (2 * v + 1)) ℂ),
        p ⬝ᵥ ((∑ j ∈ s, f j) *ᵥ p) = ∑ j ∈ s, p ⬝ᵥ (f j *ᵥ p) := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => simp [Finset.sum_insert ha, Matrix.add_mulVec, dotProduct_add, ih]
    rw [hsum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [map_add_ratCast, map_add_ratCast, map_single_one_ratCast, map_single_one_ratCast,
          map_single_one_ratCast, Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add,
          dotProduct_add, dotProduct_single_one_mulVec, dotProduct_single_one_mulVec,
          dotProduct_single_one_mulVec]
      simp only [sq, TensorNP.Eigen.xVar, TensorNP.Bilinear.xIdx]
    · rfl

namespace TensorNP.Bilinear

/-- The first two color equations force every x-coordinate to have the same cube as z. -/
theorem color_cube_eq {v : ℕ} (G : SimpleGraph (Fin v)) (p : Fin (2 * v + 1) → ℂ)
    (h : ∀ (c : Fin 4) (i : Fin v), colorEncoding G c i p = 0) (i : Fin v) :
    p (xIdx i) ^ 3 = p (zIdx v) ^ 3 := by
  have hxy : p (xIdx i) * p (yIdx i) = p (zIdx v) ^ 2 := by
    have h0 := h 0 i
    change p (xIdx i) * p (yIdx i) - p (zIdx v) ^ 2 = 0 at h0
    exact sub_eq_zero.mp h0
  have hx2 : p (xIdx i) ^ 2 = p (yIdx i) * p (zIdx v) := by
    have h1 := h 1 i
    change p (yIdx i) * p (zIdx v) - p (xIdx i) ^ 2 = 0 at h1
    exact (sub_eq_zero.mp h1).symm
  calc
    p (xIdx i) ^ 3 = p (xIdx i) * p (xIdx i) ^ 2 := by ring
    _ = p (xIdx i) * (p (yIdx i) * p (zIdx v)) := by rw [hx2]
    _ = (p (xIdx i) * p (yIdx i)) * p (zIdx v) := by ring
    _ = p (zIdx v) ^ 3 := by rw [hxy]; ring

/-- If z vanishes, the second and third equations force xᵢ = yᵢ = 0. -/
theorem color_zero_z_coordinates {v : ℕ} (G : SimpleGraph (Fin v))
    (p : Fin (2 * v + 1) → ℂ)
    (h : ∀ (c : Fin 4) (i : Fin v), colorEncoding G c i p = 0)
    (hz : p (zIdx v) = 0) (i : Fin v) : p (xIdx i) = 0 ∧ p (yIdx i) = 0 := by
  have hx := h 1 i
  have hy := h 2 i
  change p (yIdx i) * p (zIdx v) - p (xIdx i) ^ 2 = 0 at hx
  change p (xIdx i) * p (zIdx v) - p (yIdx i) ^ 2 = 0 at hy
  rw [hz] at hx hy
  simp only [mul_zero, zero_sub, neg_eq_zero] at hx hy
  exact ⟨eq_zero_of_pow_eq_zero hx, eq_zero_of_pow_eq_zero hy⟩

/-- A nonzero solution has nonzero normalization coordinate, also for v = 0. -/
theorem color_z_ne_zero {v : ℕ} (G : SimpleGraph (Fin v))
    (p : Fin (2 * v + 1) → ℂ) (hp : p ≠ 0)
    (h : ∀ (c : Fin 4) (i : Fin v), colorEncoding G c i p = 0) : p (zIdx v) ≠ 0 := by
  intro hz
  apply hp
  funext k
  change p k = 0
  by_cases hkx : k.val < v
  · let i : Fin v := ⟨k.val, hkx⟩
    have heq : xIdx i = k := Fin.ext rfl
    rw [← heq]
    exact (color_zero_z_coordinates G p h hz i).1
  · by_cases hky : k.val < 2 * v
    · let i : Fin v := ⟨k.val - v, by omega⟩
      have heq : yIdx i = k := by apply Fin.ext; simp only [yIdx, i]; omega
      rw [← heq]
      exact (color_zero_z_coordinates G p h hz i).2
    · have heq : zIdx v = k := by
        apply Fin.ext
        simp only [zIdx]
        have := k.isLt
        omega
      rw [← heq]
      exact hz

end TensorNP.Bilinear

open scoped BigOperators

/-- A vanishing neighborhood sum of cubic-root color terms has no equal-color entry. -/
theorem tensor_color_no_cancellation {ι : Type*} (s : Finset ι) (x : ℂ) (u : ι → ℂ)
    (hx : x ≠ 0) (hcube : ∀ j ∈ s, (u j)^3 = x^3)
    (hsum : ∑ j ∈ s, (x^2 + x * u j + (u j)^2) = 0) :
    ∀ j ∈ s, u j ≠ x := by
  classical
  have hterm : ∀ j ∈ s, x^2 + x * u j + (u j)^2 =
      if u j = x then 3 * x^2 else 0 := by
    intro j hj
    split_ifs with h
    · rw [h]; ring
    · have hdiff : x - u j ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      have hprod : (x - u j) * (x^2 + x * u j + (u j)^2) = 0 := by
        calc
          _ = x^3 - (u j)^3 := by ring
          _ = 0 := by rw [hcube j hj]; ring
      exact (mul_eq_zero.mp hprod).resolve_left hdiff
  have hsum' : ((s.filter fun j => u j = x).card : ℂ) * (3 * x^2) = 0 := by
    calc
      _ = ∑ j ∈ s, (if u j = x then 3 * x^2 else 0) := by
        simp [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const]
      _ = ∑ j ∈ s, (x^2 + x * u j + (u j)^2) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (hterm j hj).symm
      _ = 0 := hsum
  have hcount : (s.filter fun j => u j = x).card = 0 := by
    have hx2 : (3 : ℂ) * x^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)
    exact_mod_cast (mul_eq_zero.mp hsum').resolve_right hx2
  intro j hj heq
  have : j ∈ s.filter (fun k => u k = x) := Finset.mem_filter.mpr ⟨hj, heq⟩
  have : 0 < (s.filter fun k => u k = x).card := Finset.card_pos.mpr ⟨j, this⟩
  omega

namespace TensorNP.Bilinear

/-- The fourth color equation and common-cube property force different labels
    on adjacent vertices; the complex summands cannot cancel. -/
theorem color_adjacent_ne {v : ℕ} (G : SimpleGraph (Fin v))
    (p : Fin (2 * v + 1) → ℂ)
    (h : ∀ (c : Fin 4) (i : Fin v), colorEncoding G c i p = 0)
    (hz : p (zIdx v) ≠ 0)
    (hcube : ∀ i : Fin v, p (xIdx i) ^ 3 = p (zIdx v) ^ 3)
    (i j : Fin v) (hij : G.Adj i j) : p (xIdx i) ≠ p (xIdx j) := by
  classical
  have hx : p (xIdx i) ≠ 0 := by
    intro hi
    have hc := hcube i
    rw [hi] at hc
    have hzero : p (zIdx v) ^ 3 = 0 := by simpa using hc.symm
    exact hz (eq_zero_of_pow_eq_zero hzero)
  have hsum : ∑ k ∈ Finset.univ.filter (G.Adj i),
      (p (xIdx i) ^ 2 + p (xIdx i) * p (xIdx k) + p (xIdx k) ^ 2) = 0 := by
    have h3 := h 3 i
    change (∑ k : Fin v, if G.Adj i k then
      p (xIdx i) ^ 2 + p (xIdx i) * p (xIdx k) + p (xIdx k) ^ 2 else 0) = 0 at h3
    simpa only [Finset.sum_filter] using h3
  have heq : ∀ k ∈ Finset.univ.filter (G.Adj i),
      p (xIdx k) ^ 3 = p (xIdx i) ^ 3 := by
    intro k hk
    rw [hcube k, hcube i]
  have hki := tensor_color_no_cancellation (Finset.univ.filter (G.Adj i))
    (p (xIdx i)) (fun k ↦ p (xIdx k)) hx heq hsum j
    (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hij⟩)
  exact Ne.symm hki

end TensorNP.Bilinear


/-- A graph whose vertices are labeled by roots of one cubic, with unequal
    labels on adjacent vertices, is 3-colorable. This also covers the empty graph. -/
theorem tensor_cubic_labels_colorable {v : ℕ} (G : SimpleGraph (Fin v))
    (u : Fin v → ℂ) (c : ℂ) (hpow : ∀ i, (u i) ^ 3 = c)
    (hproper : ∀ i j, G.Adj i j → u i ≠ u j) : G.Colorable 3 := by
  classical
  let P : Polynomial ℂ := Polynomial.X ^ 3 - Polynomial.C c
  have hP : P ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by decide) c
  let S : Finset ℂ := P.roots.toFinset
  have hmem (i : Fin v) : u i ∈ S := by
    change u i ∈ P.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    simp [P, Polynomial.IsRoot.def, hpow]
  have hcard : S.card ≤ 3 := by
    calc
      S.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ 3 := Polynomial.card_roots_X_pow_sub_C (by decide) c
  have htype : Fintype.card {x // x ∈ S} ≤ Fintype.card (Fin 3) := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le htype
  refine ⟨SimpleGraph.Coloring.mk (fun i ↦ e ⟨u i, hmem i⟩) ?_⟩
  intro i j hij heq
  apply hproper i j hij
  exact congrArg Subtype.val (e.injective heq)

/-- The nontrivial direction of Hillar–Lim Lemma 2.10: a nonzero quadratic
    solution yields a proper three-coloring. -/
theorem tensor_color_quads_imply_colorable {v : ℕ} (G : SimpleGraph (Fin v)) :
    TensorNP.Eigen.QuadSolvable
      (TensorNP.Eigen.castMatrices ℂ (TensorNP.Eigen.colorEncoding G)) → G.Colorable 3 := by
  intro hq
  obtain ⟨p, hp, hq⟩ := hq
  have hb : ∀ (c : Fin 4) (i : Fin v), TensorNP.Bilinear.colorEncoding G c i p = 0 := by
    intro c i
    rw [← eigen_quad_eq_bilin]
    exact hq (c, i)
  have hz := TensorNP.Bilinear.color_z_ne_zero G p hp hb
  have hc : ∀ i : Fin v, p (TensorNP.Bilinear.xIdx i) ^ 3 =
      p (TensorNP.Bilinear.zIdx v) ^ 3 := TensorNP.Bilinear.color_cube_eq G p hb
  apply tensor_cubic_labels_colorable G (fun i ↦ p (TensorNP.Bilinear.xIdx i))
    (p (TensorNP.Bilinear.zIdx v) ^ 3) hc
  intro i j hij
  exact TensorNP.Bilinear.color_adjacent_ne G p hb hz hc i j hij

open TensorNP.Eigen

private def root (ω : ℂ) : Fin 3 → ℂ := ![1, ω, ω ^ 2]
private def rootInv (ω : ℂ) : Fin 3 → ℂ := ![1, ω ^ 2, ω]

private lemma root_props (ω : ℂ) (hw : ω ^ 2 + ω + 1 = 0) (i : Fin 3) :
    root ω i * rootInv ω i = 1 ∧ rootInv ω i = root ω i ^ 2 ∧
      root ω i = rootInv ω i ^ 2 := by
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hw
  have h4 : ω ^ 4 = ω := by linear_combination (ω ^ 2 - ω) * hw
  fin_cases i <;> simp [root, rootInv] <;> constructor <;>
    first | linear_combination h3 | linear_combination -h3 |
      linear_combination h4 | linear_combination -h4

private lemma root_pair (ω : ℂ) (hw : ω ^ 2 + ω + 1 = 0) (i j : Fin 3) (hij : i ≠ j) :
    root ω i ^ 2 + root ω i * root ω j + root ω j ^ 2 = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [root] <;>
    first | linear_combination hw | linear_combination ω * hw |
      linear_combination (ω ^ 2) * hw | linear_combination (ω ^ 2 - ω + 1) * hw

private lemma primitive_exists : ∃ ω : ℂ, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ 3
  refine ⟨ω, ?_⟩
  have h1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have h3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hp : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr h1)

private def witness {v : ℕ} (c : Fin v → Fin 3) (ω : ℂ) (k : Fin (2 * v + 1)) : ℂ :=
  if hk : k.val < v then root ω (c ⟨k.val, hk⟩)
  else if hk : k.val < 2 * v then rootInv ω (c ⟨k.val - v, by omega⟩)
  else 1

private lemma witness_x {v : ℕ} (c : Fin v → Fin 3) (ω : ℂ) (i : Fin v) :
    witness c ω (xVar i) = root ω (c i) := by
  simp [witness, xVar, i.isLt]

private lemma witness_y {v : ℕ} (c : Fin v → Fin 3) (ω : ℂ) (i : Fin v) :
    witness c ω (yVar i) = rootInv ω (c i) := by
  unfold witness
  split_ifs with h1 h2
  · have hi := i.isLt
    simp only [yVar, Fin.val_mk] at h1
    omega
  · congr 2
    apply Fin.ext
    simp [yVar]
  · have hi := i.isLt
    simp only [yVar, Fin.val_mk] at h2
    omega

private lemma witness_z {v : ℕ} (c : Fin v → Fin 3) (ω : ℂ) :
    witness c ω zVar = 1 := by
  unfold witness
  split_ifs with h1 h2
  · simp only [zVar, Fin.val_mk] at h1
    omega
  · simp only [zVar, Fin.val_mk] at h2
    omega
  · rfl



theorem colorable_implies_quad {v : ℕ} (G : SimpleGraph (Fin v)) (h : G.Colorable 3) :
    QuadSolvable (castMatrices ℂ (colorEncoding G)) := by
  classical
  obtain ⟨c⟩ := h
  obtain ⟨ω, hω⟩ := primitive_exists
  refine ⟨witness c ω, ?_, ?_⟩
  · intro heq
    have hz := congrFun heq (zVar (v := v))
    simpa [witness_z] using hz
  · rintro ⟨a, i⟩
    rw [eigen_quad_eq_bilin]
    have hx (j : Fin v) : TensorNP.Bilinear.xIdx j = xVar j := rfl
    have hy (j : Fin v) : TensorNP.Bilinear.yIdx j = yVar j := rfl
    have hz : TensorNP.Bilinear.zIdx v = zVar := rfl
    fin_cases a
    · have hp := (root_props ω hω (c i)).1
      simpa only [TensorNP.Bilinear.colorEncoding, hx, hy, hz, witness_x, witness_y, witness_z,
        one_pow, sub_eq_zero] using hp
    · have hp := (root_props ω hω (c i)).2.1
      simpa only [TensorNP.Bilinear.colorEncoding, hx, hy, hz, witness_x, witness_y, witness_z,
        mul_one, sub_eq_zero] using hp
    · have hp := (root_props ω hω (c i)).2.2
      simpa only [TensorNP.Bilinear.colorEncoding, hx, hy, hz, witness_x, witness_y, witness_z,
        mul_one, sub_eq_zero] using hp
    · simp only [TensorNP.Bilinear.colorEncoding]
      apply Finset.sum_eq_zero
      intro j hj
      split_ifs with hij
      · have hp := root_pair ω hω (c i) (c j) (c.valid hij)
        simpa only [hx, witness_x] using hp
      · rfl

/-- Hillar–Lim Lemma 2.10 for the exact rational matrix color encoding. -/
theorem solution {v : ℕ} (G : SimpleGraph (Fin v)) :
    TensorNP.Eigen.QuadSolvable
      (TensorNP.Eigen.castMatrices ℂ (TensorNP.Eigen.colorEncoding G)) ↔ G.Colorable 3 := by
  exact ⟨tensor_color_quads_imply_colorable G, colorable_implies_quad G⟩
