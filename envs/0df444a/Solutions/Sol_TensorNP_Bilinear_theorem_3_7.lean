-- Prove2me | solution 1 for TensorNP.Bilinear.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T19:57:45.440231+00:00
-- url     : https://prove2.me/submissions/1466b028-9ead-4b17-9351-b3e0dbd6c3e2

import Mathlib
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_StackProgPortLift
import Definitions.Def_TensorNP_Bilinear_Construction
import Definitions.Def_TensorNP_Bilinear_Encoding
import Definitions.Def_TensorNP_Eigen_Construction
import Definitions.Def_TensorNP_Eigen_Defs
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_unary_to_encNat_stack
import Theorems.Thm_StackProgPortLift_liftProgC_exec
import Theorems.Thm_TensorAdjacencyLookup8_lookupProg_exec


/- Inlined module: BilinearFoundation -/
section
-- Independent root audit of actual semantic bodies and encoding/layout proofs.

namespace TensorNP.BilinearAudit.Minors

set_option autoImplicit false

open TensorNP.Bilinear

theorem _root_.TensorNP.Bilinear.minors_vanish_iff_proportional {N : ℕ} (v w : Fin N → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    (∀ ab : MinorIdx N, ∑ p, ∑ q, (minorSlice ab p q : ℂ) * v p * w q = 0) ↔
      ∃ c : ℂ, v = c • w := by
  have key : ∀ ab : MinorIdx N, ∑ p, ∑ q, (minorSlice ab p q : ℂ) * v p * w q =
      v ab.1.1 * w ab.1.2 - v ab.1.2 * w ab.1.1 := by
    intro ab
    simp only [minorSlice]
    push_cast
    simp [sub_mul, Finset.sum_sub_distrib, ite_and]
  constructor
  · intro h
    have hh : ∀ a b : Fin N, v a * w b = v b * w a := by
      intro a b
      rcases lt_trichotomy a b with hab | hab | hab
      · have := h ⟨(a, b), hab⟩
        rw [key] at this
        exact sub_eq_zero.mp this
      · rw [hab]
      · have := h ⟨(b, a), hab⟩
        rw [key] at this
        exact (sub_eq_zero.mp this).symm
    obtain ⟨b, hb⟩ : ∃ b, w b ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hw (funext hcon)
    refine ⟨v b / w b, ?_⟩
    funext a
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    have := hh a b
    linear_combination this
  · rintro ⟨c, rfl⟩ ab
    rw [key]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end TensorNP.BilinearAudit.Minors

section EigenSemanticAudit

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
theorem TensorNP.Eigen.lemma_2_10 {v : ℕ} (G : SimpleGraph (Fin v)) :
    TensorNP.Eigen.QuadSolvable
      (TensorNP.Eigen.castMatrices ℂ (TensorNP.Eigen.colorEncoding G)) ↔ G.Colorable 3 := by
  exact ⟨tensor_color_quads_imply_colorable G, colorable_implies_quad G⟩

end EigenSemanticAudit

namespace TensorNP.BilinearAudit.Color

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

theorem _root_.TensorNP.Bilinear.lemma_2_10 {v : ℕ} (G : SimpleGraph (Fin v)) :
    (∃ p : Fin (2 * v + 1) → ℂ, p ≠ 0 ∧ ∀ (c : Fin 4) (i : Fin v),
        TensorNP.Bilinear.colorEncoding G c i p = 0) ↔
      G.Colorable 3 := by
  rw [← TensorNP.Eigen.lemma_2_10 G]
  unfold TensorNP.Eigen.QuadSolvable
  simp [Prod.forall, eigen_quad_eq_bilin]

end TensorNP.BilinearAudit.Color

namespace TensorNP.BilinearAudit.AG

open TensorNP.Bilinear

private lemma minor_count_lower {v : ℕ} (hv : 0 < v) :
    3 ≤ Fintype.card (MinorIdx (2 * v + 1)) := by
  classical
  have hn : 2 < 2 * v + 1 := by omega
  let a : Fin (2 * v + 1) := ⟨0, by omega⟩
  let b : Fin (2 * v + 1) := ⟨1, by omega⟩
  let c : Fin (2 * v + 1) := ⟨2, by omega⟩
  let f : Fin 3 → MinorIdx (2 * v + 1) :=
    ![⟨(a, b), by change (0 : ℕ) < 1; omega⟩,
      ⟨(a, c), by change (0 : ℕ) < 2; omega⟩,
      ⟨(b, c), by change (1 : ℕ) < 2; omega⟩]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f, a, b, c, Subtype.ext_iff, Prod.ext_iff]
  have h := Fintype.card_le_of_injective f hf
  simpa using h

private lemma slice_count_lower {v : ℕ} (hv : 0 < v) :
    Fintype.card (Fin (2 * v + 1) ⊕ Fin (2 * v + 1)) < Fintype.card (SliceIdx v) := by
  have h := minor_count_lower hv
  simp only [SliceIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

private lemma nonzero_kernel {v : ℕ} (hv : 0 < v)
    (L : (SliceIdx v → ℂ) →ₗ[ℂ] (Fin (2 * v + 1) ⊕ Fin (2 * v + 1) → ℂ)) :
    ∃ x, x ≠ 0 ∧ L x = 0 := by
  have hn : ¬ Function.Injective L := by
    intro hi
    have hdim := LinearMap.finrank_le_finrank_of_injective hi
    simp only [Module.finrank_fintype_fun_eq_card] at hdim
    have h := slice_count_lower hv
    omega
  have hn' : ∃ x y, L x = L y ∧ x ≠ y := by
    by_contra h
    apply hn
    intro x y heq
    by_contra hne
    exact h ⟨x, y, heq, hne⟩
  obtain ⟨x, y, hxy, hne⟩ := hn'
  refine ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
  simp [map_sub, hxy]

private noncomputable def constraintMap {v : ℕ} (G : SimpleGraph (Fin v))
    (p : Fin (2 * v + 1) → ℂ) :
    (SliceIdx v → ℂ) →ₗ[ℂ] (Fin (2 * v + 1) ⊕ Fin (2 * v + 1) → ℂ) where
  toFun u := Sum.elim
    (fun j ↦ ∑ s, ∑ k, (AG G s j k : ℂ) * u s * p k)
    (fun k ↦ ∑ s, ∑ j, (AG G s j k : ℂ) * u s * p j)
  map_add' u u' := by
    funext x
    cases x <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
      mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by
    funext x
    cases x <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, RingHom.id_apply] <;>
      apply Finset.sum_congr rfl <;> intro s _ <;>
      apply Finset.sum_congr rfl <;> intro k _ <;> ring

private lemma exists_slice_weights {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v))
    (p : Fin (2 * v + 1) → ℂ) :
    ∃ u : SliceIdx v → ℂ, u ≠ 0 ∧
      (∀ j, ∑ s, ∑ k, (AG G s j k : ℂ) * u s * p k = 0) ∧
      (∀ k, ∑ s, ∑ j, (AG G s j k : ℂ) * u s * p j = 0) := by
  obtain ⟨u, hu, hL⟩ := nonzero_kernel hv (constraintMap G p)
  refine ⟨u, hu, ?_, ?_⟩
  · intro j
    have := congrFun hL (Sum.inl j)
    simpa [constraintMap] using this
  · intro k
    have := congrFun hL (Sum.inr k)
    simpa [constraintMap] using this

private lemma unit_eval {N : ℕ} (a b : Fin N) (p q : Fin N → ℂ) :
    ∑ j, ∑ k, (unitMat a b j k : ℂ) * p j * q k = p a * q b := by
  classical
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [unitMat]
    · intro j _ hj
      simp [unitMat, hj]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · intro i _ hi
    simp [unitMat, hi]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private lemma minor_eval {N : ℕ} (ab : MinorIdx N) (p q : Fin N → ℂ) :
    ∑ j, ∑ k, (minorSlice ab j k : ℂ) * p j * q k =
      p ab.1.1 * q ab.1.2 - p ab.1.2 * q ab.1.1 := by
  classical
  simp only [minorSlice, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  rw [show (∑ j, ∑ k, ((if j = ab.1.1 ∧ k = ab.1.2 then 1 else 0 : ℤ) : ℂ) * p j * q k) =
      p ab.1.1 * q ab.1.2 from unit_eval _ _ _ _,
      show (∑ j, ∑ k, ((if j = ab.1.2 ∧ k = ab.1.1 then 1 else 0 : ℤ) : ℂ) * p j * q k) =
      p ab.1.2 * q ab.1.1 from unit_eval _ _ _ _]

private lemma cube_slices {v : ℕ} (G : SimpleGraph (Fin v)) (c : Fin 3) (i : Fin v)
    (p : Fin (2*v+1) → ℂ) :
    (∑ j, ∑ k, (AG G (Sum.inr (Sum.inl (c,i))) j k : ℂ) * p j * p k) =
      colorEncoding G (Fin.castSucc c) i p := by
  classical
  fin_cases c <;> simp only [AG, Int.cast_sub, sub_mul, Finset.sum_sub_distrib, unit_eval,
    colorEncoding, Fin.castSucc_mk, pow_two]

private lemma minor_slices {v : ℕ} (G : SimpleGraph (Fin v)) (ab : MinorIdx (2*v+1))
    (p : Fin (2*v+1) → ℂ) :
    (∑ j, ∑ k, (AG G (Sum.inl ab) j k : ℂ) * p j * p k) = 0 := by
  rw [show (∑ j, ∑ k, (AG G (Sum.inl ab) j k : ℂ) * p j * p k) =
    ∑ j, ∑ k, (minorSlice ab j k : ℂ) * p j * p k from rfl, minor_eval]
  ring

private lemma edge_slices {v : ℕ} (G : SimpleGraph (Fin v)) (i : Fin v)
    (p : Fin (2*v+1) → ℂ) :
    (∑ j, ∑ k, (AG G (Sum.inr (Sum.inr i)) j k : ℂ) * p j * p k) =
      colorEncoding G 3 i p := by
  classical
  simp only [AG, colorEncoding, Int.cast_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs with hadj
  · simp only [Int.cast_ite, Int.cast_add, Int.cast_zero, add_mul, zero_mul,
      Finset.sum_add_distrib, unit_eval, pow_two]
  · simp

private lemma scalar_eval {v : ℕ} (G : SimpleGraph (Fin v)) (s : SliceIdx v)
    (c : ℂ) (p : Fin (2 * v + 1) → ℂ) :
    (∑ j, ∑ k, (AG G s j k : ℂ) * (c * p j) * p k) =
      c * (∑ j, ∑ k, (AG G s j k : ℂ) * p j * p k) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem _root_.TensorNP.Bilinear.AG_feasible_iff_colorable {v : ℕ} (G : SimpleGraph (Fin v)) (hv : 0 < v) :
    TBF (fun s p q ↦ (AG G s p q : ℂ)) ↔ G.Colorable 3 := by
  constructor
  · rintro ⟨u, p, q, hu, hp, hq, h1, h2, h3⟩
    have hminor : ∀ ab : MinorIdx (2 * v + 1),
        ∑ j, ∑ k, (minorSlice ab j k : ℂ) * p j * q k = 0 := by
      intro ab
      exact h1 (Sum.inl ab)
    obtain ⟨c, hc⟩ := (minors_vanish_iff_proportional p q hp hq).mp hminor
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hp
      rw [hc, hc0]
      simp
    have hdiag (s : SliceIdx v) :
        (∑ j, ∑ k, (AG G s j k : ℂ) * q j * q k) = 0 := by
      have h := h1 s
      rw [hc] at h
      simp only [Pi.smul_apply, smul_eq_mul, scalar_eval] at h
      exact (mul_eq_zero.mp h).resolve_left hc0
    apply (lemma_2_10 G).mp
    refine ⟨q, hq, ?_⟩
    intro a i
    fin_cases a
    · have h := hdiag (Sum.inr (Sum.inl ((0 : Fin 3), i)))
      rw [cube_slices] at h
      exact h
    · have h := hdiag (Sum.inr (Sum.inl ((1 : Fin 3), i)))
      rw [cube_slices] at h
      exact h
    · have h := hdiag (Sum.inr (Sum.inl ((2 : Fin 3), i)))
      rw [cube_slices] at h
      exact h
    · have h := hdiag (Sum.inr (Sum.inr i))
      rw [edge_slices] at h
      exact h
  · intro hc
    obtain ⟨p, hp, hpolys⟩ := (lemma_2_10 G).mpr hc
    obtain ⟨u, hu, h2, h3⟩ := exists_slice_weights hv G p
    refine ⟨u, p, p, hu, hp, hp, ?_, h2, h3⟩
    intro s
    cases s with
    | inl ab => exact minor_slices G ab p
    | inr other =>
      cases other with
      | inl ci =>
        rcases ci with ⟨c, i⟩
        rw [cube_slices]
        exact hpolys (Fin.castSucc c) i
      | inr i =>
        rw [edge_slices]
        exact hpolys 3 i

end TensorNP.BilinearAudit.AG

namespace TensorNP.BilinearAudit.Doubling

open Finset TensorNP.Bilinear

private def asComplex {I : Type} (x : I ⊕ I → ℝ) (i : I) : ℂ :=
  ⟨x (Sum.inl i), x (Sum.inr i)⟩

private def asReal {I : Type} (x : I → ℂ) : I ⊕ I → ℝ :=
  Sum.elim (fun i ↦ (x i).re) (fun i ↦ (x i).im)

private lemma asComplex_asReal {I : Type} (x : I → ℂ) : asComplex (asReal x) = x := by
  funext i
  exact Complex.ext rfl rfl

private lemma asReal_asComplex {I : Type} (x : I ⊕ I → ℝ) : asReal (asComplex x) = x := by
  funext i
  cases i <;> rfl

private lemma real_first {I J K : Type} [Fintype J] [Fintype K]
    (A : I → J → K → ℝ) (v : J ⊕ J → ℝ) (w : K ⊕ K → ℝ) (i : I) :
    (∑ j, ∑ k, (A i j k : ℂ) * asComplex v j * asComplex w k).re =
      ∑ j, ∑ k, doubling A (Sum.inl i) j k * v j * w k := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, asComplex,
    Fintype.sum_sum_type, doubling, neg_mul, zero_add, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero]
  ring

private lemma imag_first {I J K : Type} [Fintype J] [Fintype K]
    (A : I → J → K → ℝ) (v : J ⊕ J → ℝ) (w : K ⊕ K → ℝ) (i : I) :
    (∑ j, ∑ k, (A i j k : ℂ) * asComplex v j * asComplex w k).im =
      ∑ j, ∑ k, doubling A (Sum.inr i) j k * v j * w k := by
  simp only [Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, asComplex,
    Fintype.sum_sum_type, doubling, neg_mul, zero_add, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero]
  ring

private lemma real_second {I J K : Type} [Fintype I] [Fintype K]
    (A : I → J → K → ℝ) (u : I ⊕ I → ℝ) (w : K ⊕ K → ℝ) (j : J) :
    (∑ i, ∑ k, (A i j k : ℂ) * starRingEnd ℂ (asComplex u i) * asComplex w k).re =
      ∑ i, ∑ k, doubling A i (Sum.inl j) k * u i * w k := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, asComplex,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Fintype.sum_sum_type,
    doubling, neg_mul, mul_neg, zero_add, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero]
  ring

private lemma imag_second {I J K : Type} [Fintype I] [Fintype K]
    (A : I → J → K → ℝ) (u : I ⊕ I → ℝ) (w : K ⊕ K → ℝ) (j : J) :
    (∑ i, ∑ k, (A i j k : ℂ) * starRingEnd ℂ (asComplex u i) * asComplex w k).im =
      -(∑ i, ∑ k, doubling A i (Sum.inr j) k * u i * w k) := by
  simp only [Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, asComplex,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Fintype.sum_sum_type,
    doubling, neg_mul, mul_neg, zero_add, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero]
  ring

private lemma real_third {I J K : Type} [Fintype I] [Fintype J]
    (A : I → J → K → ℝ) (u : I ⊕ I → ℝ) (v : J ⊕ J → ℝ) (k : K) :
    (∑ i, ∑ j, (A i j k : ℂ) * starRingEnd ℂ (asComplex u i) * asComplex v j).re =
      ∑ i, ∑ j, doubling A i j (Sum.inl k) * u i * v j := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, asComplex,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Fintype.sum_sum_type,
    doubling, neg_mul, mul_neg, zero_add, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero]
  ring

private lemma imag_third {I J K : Type} [Fintype I] [Fintype J]
    (A : I → J → K → ℝ) (u : I ⊕ I → ℝ) (v : J ⊕ J → ℝ) (k : K) :
    (∑ i, ∑ j, (A i j k : ℂ) * starRingEnd ℂ (asComplex u i) * asComplex v j).im =
      -(∑ i, ∑ j, doubling A i j (Sum.inr k) * u i * v j) := by
  simp only [Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, asComplex,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Fintype.sum_sum_type,
    doubling, neg_mul, mul_neg, zero_add, add_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const_zero]
  ring

private lemma asReal_zero {I : Type} : asReal (0 : I → ℂ) = 0 := by
  funext i
  cases i <;> simp [asReal]

private lemma asComplex_zero {I : Type} : asComplex (0 : I ⊕ I → ℝ) = 0 := by
  funext i
  apply Complex.ext <;> simp [asComplex]

private lemma asReal_ne {I : Type} {x : I → ℂ} (hx : x ≠ 0) : asReal x ≠ 0 := by
  intro h
  apply hx
  have h' := congrArg asComplex h
  simpa [asComplex_asReal, asComplex_zero] using h'

private lemma asComplex_ne {I : Type} {x : I ⊕ I → ℝ} (hx : x ≠ 0) : asComplex x ≠ 0 := by
  intro h
  apply hx
  have h' := congrArg asReal h
  simpa [asReal_asComplex, asReal_zero] using h'

private lemma conj_ne {I : Type} {x : I → ℂ} (hx : x ≠ 0) :
    (fun i ↦ starRingEnd ℂ (x i)) ≠ 0 := by
  intro h
  apply hx
  funext i
  have hi := congrFun h i
  have hh := congrArg (starRingEnd ℂ) hi
  simpa using hh

theorem _root_.TensorNP.Bilinear.lemma_3_6 {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ) :
    TBF (doubling A) ↔ TBF (fun i j k ↦ (A i j k : ℂ)) := by
  constructor
  · rintro ⟨u, v, w, hu, hv, hw, h1, h2, h3⟩
    refine ⟨(fun i ↦ starRingEnd ℂ (asComplex u i)), asComplex v, asComplex w,
      conj_ne (asComplex_ne hu), asComplex_ne hv, asComplex_ne hw, ?_, ?_, ?_⟩
    · intro i
      apply Complex.ext
      · rw [real_first, h1]
        rfl
      · rw [imag_first, h1]
        rfl
    · intro j
      apply Complex.ext
      · rw [real_second, h2]
        rfl
      · rw [imag_second, h2]
        simp
    · intro k
      apply Complex.ext
      · rw [real_third, h3]
        rfl
      · rw [imag_third, h3]
        simp
  · rintro ⟨u, v, w, hu, hv, hw, h1, h2, h3⟩
    let ur := asReal (fun i ↦ starRingEnd ℂ (u i))
    let vr := asReal v
    let wr := asReal w
    have hu' : (fun i ↦ starRingEnd ℂ (asComplex ur i)) = u := by
      funext i
      simp [ur, asComplex_asReal]
    have hv' : asComplex vr = v := asComplex_asReal v
    have hw' : asComplex wr = w := asComplex_asReal w
    refine ⟨ur, vr, wr, asReal_ne (conj_ne hu), asReal_ne hv, asReal_ne hw, ?_, ?_, ?_⟩
    · intro i
      cases i with
      | inl i =>
        have hh := congrArg Complex.re (h1 i)
        rw [← hv', ← hw', real_first] at hh
        simpa using hh
      | inr i =>
        have hh := congrArg Complex.im (h1 i)
        rw [← hv', ← hw', imag_first] at hh
        simpa using hh
    · intro j
      cases j with
      | inl j =>
        have hh := congrArg Complex.re (h2 j)
        rw [← hu', ← hw', real_second] at hh
        simpa using hh
      | inr j =>
        have hh := congrArg Complex.im (h2 j)
        rw [← hu', ← hw', imag_second] at hh
        exact neg_eq_zero.mp (by simpa only [Complex.zero_im] using hh)
    · intro k
      cases k with
      | inl k =>
        have hh := congrArg Complex.re (h3 k)
        rw [← hu', ← hv', real_third] at hh
        simpa using hh
      | inr k =>
        have hh := congrArg Complex.im (h3 k)
        rw [← hu', ← hv', imag_third] at hh
        exact neg_eq_zero.mp (by simpa only [Complex.zero_im] using hh)

end TensorNP.BilinearAudit.Doubling


set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.BilinearCode

/-- Read the binary digits of the first separator-terminated code.  This is a
    mathematical decoder, not yet a stack or Turing-machine program. -/
private def readFirstBits : List BSym → List Bool
  | .zero :: rest => false :: readFirstBits rest
  | .one :: rest => true :: readFirstBits rest
  | _ => []

private theorem readFirstBits_digits (digits : List Bool) (tail : List BSym) :
    readFirstBits ((digits.map fun b ↦ if b then BSym.one else BSym.zero) ++ BSym.sep :: tail) =
      digits := by
  induction digits with
  | nil => rfl
  | cons b digits ih =>
    cases b <;> simp [readFirstBits, ih]

private theorem readFirstBits_encNat (n : ℕ) (tail : List BSym) :
    readFirstBits (encNat n ++ tail) = n.bits := by
  simpa [encNat, List.append_assoc] using readFirstBits_digits n.bits tail

private theorem encNat_not_nil (n : ℕ) : encNat n ≠ [] := by
  simp [encNat]

/-- Canonical binary natural-number codes are uniquely decodable from the front,
    even in the presence of arbitrary trailing input. -/
theorem tensor_encNat_prefix_unique (m n : ℕ) (s t : List BSym)
    (h : encNat m ++ s = encNat n ++ t) : m = n ∧ s = t := by
  have hb : m.bits = n.bits := by
    have he := congrArg readFirstBits h
    simpa only [readFirstBits_encNat] using he
  have hmn : m = n := by
    apply Nat.eq_of_testBit_eq
    intro i
    simpa only [Nat.testBit_eq_inth] using congrArg (fun bs : List Bool ↦ bs.getI i) hb
  subst n
  exact ⟨rfl, (List.append_right_inj (encNat m)).mp h⟩

/-- A canonical sequence of separator-terminated natural-number codes uniquely
    determines the encoded natural-number list. -/
theorem tensor_encNats_injective : Function.Injective encNats := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys =>
      have h' : encNat y ++ encNats ys = [] := by simpa [encNats] using h.symm
      exact False.elim (encNat_not_nil y (List.append_eq_nil_iff.mp h').1)
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have h' : encNat x ++ encNats xs = [] := by simpa [encNats] using h
      exact False.elim (encNat_not_nil x (List.append_eq_nil_iff.mp h').1)
    | cons y ys =>
      have h' : encNat x ++ encNats xs = encNat y ++ encNats ys := by
        simpa [encNats] using h
      obtain ⟨hxy, htail⟩ := tensor_encNat_prefix_unique x y (encNats xs) (encNats ys) h'
      have hxs : xs = ys := ih htail
      simp [hxy, hxs]


private theorem encNat_head_ne_minus (n : ℕ) (tail : List BSym) :
    (encNat n ++ tail).head? ≠ some BSym.minus := by
  unfold encNat
  cases n.bits with
  | nil => simp
  | cons b bs => cases b <;> simp

/-- Signed binary integer codes are also prefix-unique, including their
    optional leading minus sign and the remaining input. -/
theorem tensor_encInt_prefix_unique (m n : ℤ) (s t : List BSym)
    (h : encInt m ++ s = encInt n ++ t) : m = n ∧ s = t := by
  by_cases hm : m < 0
  · by_cases hn : n < 0
    · have h' : encNat m.natAbs ++ s = encNat n.natAbs ++ t := by
        simpa [encInt, hm, hn, List.append_assoc] using h
      obtain ⟨ha, ht⟩ := tensor_encNat_prefix_unique m.natAbs n.natAbs s t h'
      have hz := congrArg (fun x : ℕ ↦ (x : ℤ)) ha
      rw [Int.ofNat_natAbs_of_nonpos (le_of_lt hm),
        Int.ofNat_natAbs_of_nonpos (le_of_lt hn)] at hz
      have heq : m = n := by omega
      exact ⟨heq, ht⟩
    · have hh := congrArg List.head? h
      have hbad : (encNat n.natAbs ++ t).head? = some BSym.minus := by
        simpa [encInt, hm, hn, List.append_assoc] using hh.symm
      exact False.elim (encNat_head_ne_minus n.natAbs t hbad)
  · by_cases hn : n < 0
    · have hh := congrArg List.head? h
      have hbad : (encNat m.natAbs ++ s).head? = some BSym.minus := by
        simpa [encInt, hm, hn, List.append_assoc] using hh
      exact False.elim (encNat_head_ne_minus m.natAbs s hbad)
    · have h' : encNat m.natAbs ++ s = encNat n.natAbs ++ t := by
        simpa [encInt, hm, hn, List.append_assoc] using h
      obtain ⟨ha, ht⟩ := tensor_encNat_prefix_unique m.natAbs n.natAbs s t h'
      have hz := congrArg (fun x : ℕ ↦ (x : ℤ)) ha
      rw [Int.ofNat_natAbs_of_nonneg (le_of_not_gt hm),
        Int.ofNat_natAbs_of_nonneg (le_of_not_gt hn)] at hz
      exact ⟨hz, ht⟩

/-- The exact numerator/denominator encoding used by tensorCode is
    prefix-unique for rationals and preserves the unconsumed suffix. -/
theorem tensor_encRat_prefix_unique (q r : ℚ) (s t : List BSym)
    (h : TensorNP.Eigen.encRat q ++ s = TensorNP.Eigen.encRat r ++ t) : q = r ∧ s = t := by
  have h' : encInt q.num ++ (encNat q.den ++ s) = encInt r.num ++ (encNat r.den ++ t) := by
    simpa [TensorNP.Eigen.encRat, List.append_assoc] using h
  obtain ⟨hnum, hrest⟩ := tensor_encInt_prefix_unique q.num r.num _ _ h'
  obtain ⟨hden, htail⟩ := tensor_encNat_prefix_unique q.den r.den s t hrest
  exact ⟨Rat.ext hnum hden, htail⟩


private theorem encRat_not_nil (q : ℚ) : TensorNP.Eigen.encRat q ≠ [] := by
  intro h
  have h' : encInt q.num = [] ∧ encNat q.den = [] := by
    apply List.append_eq_nil_iff.mp
    simpa [TensorNP.Eigen.encRat] using h
  exact encNat_not_nil q.den h'.2

private def encodeRatList (xs : List ℚ) : List BSym := xs.flatMap TensorNP.Eigen.encRat

/-- A concatenation of canonical rational codes uniquely determines the
    entire rational list. -/
theorem tensor_encRatList_injective : Function.Injective encodeRatList := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys =>
      have h' : TensorNP.Eigen.encRat y ++ encodeRatList ys = [] := by
        simpa [encodeRatList] using h.symm
      exact False.elim (encRat_not_nil y (List.append_eq_nil_iff.mp h').1)
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have h' : TensorNP.Eigen.encRat x ++ encodeRatList xs = [] := by
        simpa [encodeRatList] using h
      exact False.elim (encRat_not_nil x (List.append_eq_nil_iff.mp h').1)
    | cons y ys =>
      have h' : TensorNP.Eigen.encRat x ++ encodeRatList xs =
          TensorNP.Eigen.encRat y ++ encodeRatList ys := by
        simpa [encodeRatList] using h
      obtain ⟨hxy, htail⟩ := tensor_encRat_prefix_unique x y (encodeRatList xs) (encodeRatList ys) h'
      have hxs : xs = ys := ih htail
      simp [hxy, hxs]


/-- A row-major flattening of a fixed rectangular matrix determines every
    entry, even when one of its dimensions is zero. -/
theorem tensor_matrix_flatten_injective {α : Type} {r c : ℕ}
    (f g : Fin r → Fin c → α)
    (h : (List.ofFn fun i ↦ List.ofFn (f i)).flatten =
      (List.ofFn fun i ↦ List.ofFn (g i)).flatten) : f = g := by
  induction r with
  | zero =>
    funext i
    exact Fin.elim0 i
  | succ r ih =>
    have h' : List.ofFn (f 0) ++ (List.ofFn fun i : Fin r ↦ List.ofFn (f i.succ)).flatten =
        List.ofFn (g 0) ++ (List.ofFn fun i : Fin r ↦ List.ofFn (g i.succ)).flatten := by
      simpa [List.ofFn_succ] using h
    have hrow : f 0 = g 0 := List.ofFn_injective (List.append_inj_left h' (by simp))
    have htail := List.append_inj_right h' (by simp)
    have hs : (fun i : Fin r ↦ f i.succ) = (fun i : Fin r ↦ g i.succ) := ih _ _ htail
    funext i
    refine Fin.cases ?_ ?_ i
    · exact hrow
    · intro j
      exact congrFun hs j



/-- Flattening equal-length blocks is injective on their ordered family. -/
private theorem equal_blocks_flatten_injective {α : Type} {n L : ℕ}
    (f g : Fin n → List α) (hf : ∀ i, (f i).length = L) (hg : ∀ i, (g i).length = L)
    (h : (List.ofFn f).flatten = (List.ofFn g).flatten) : f = g := by
  induction n with
  | zero =>
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    have h' : f 0 ++ (List.ofFn fun i : Fin n ↦ f i.succ).flatten =
        g 0 ++ (List.ofFn fun i : Fin n ↦ g i.succ).flatten := by
      simpa [List.ofFn_succ] using h
    have hlen : (f 0).length = (g 0).length := by rw [hf 0, hg 0]
    have hhead : f 0 = g 0 := List.append_inj_left h' hlen
    have htail := List.append_inj_right h' hlen
    have hs : (fun i : Fin n ↦ f i.succ) = (fun i : Fin n ↦ g i.succ) :=
      ih _ _ (fun i ↦ hf i.succ) (fun i ↦ hg i.succ) htail
    funext i
    refine Fin.cases ?_ ?_ i
    · exact hhead
    · intro j
      exact congrFun hs j


private def tensorEntries {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℚ) : List ℚ :=
  (List.ofFn fun i : Fin l ↦ (List.ofFn fun j : Fin m ↦ List.ofFn (A i j)).flatten).flatten

private theorem tensorCode_as_entries {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℚ) :
    TensorNP.Bilinear.tensorCode A = encNat l ++ (encNat m ++ (encNat n ++ encodeRatList (tensorEntries A))) := by
  simp [TensorNP.Bilinear.tensorCode, encNats, encodeRatList, tensorEntries, List.flatMap_def,
    List.map_flatten, List.flatten_flatten, List.map_ofFn, Function.comp_def, List.append_assoc]

theorem tensorCode_injective_fixed {l m n : ℕ} :
    Function.Injective (TensorNP.Bilinear.tensorCode (l := l) (m := m) (n := n)) := by
  intro A B h
  rw [tensorCode_as_entries, tensorCode_as_entries] at h
  have hentry : tensorEntries A = tensorEntries B :=
    tensor_encRatList_injective ((List.append_right_inj (encNat n)).mp
      ((List.append_right_inj (encNat m)).mp ((List.append_right_inj (encNat l)).mp h)))
  let rowA : Fin l → List ℚ := fun i ↦ (List.ofFn fun j : Fin m ↦ List.ofFn (A i j)).flatten
  let rowB : Fin l → List ℚ := fun i ↦ (List.ofFn fun j : Fin m ↦ List.ofFn (B i j)).flatten
  have hlenA (i : Fin l) : (rowA i).length = m*n := by
    simp [rowA, List.length_flatten, List.map_ofFn, Function.comp_def,
      List.length_ofFn, List.ofFn_const]
  have hlenB (i : Fin l) : (rowB i).length = m*n := by
    simp [rowB, List.length_flatten, List.map_ofFn, Function.comp_def,
      List.length_ofFn, List.ofFn_const]
  have hrows : rowA = rowB := equal_blocks_flatten_injective rowA rowB hlenA hlenB hentry
  funext i
  apply tensor_matrix_flatten_injective
  exact congrFun hrows i

theorem tensorCode_dimensions_unique {l m n l' m' n' : ℕ}
    (A : Fin l → Fin m → Fin n → ℚ) (B : Fin l' → Fin m' → Fin n' → ℚ)
    (h : TensorNP.Bilinear.tensorCode A = TensorNP.Bilinear.tensorCode B) :
    l = l' ∧ m = m' ∧ n = n' := by
  rw [tensorCode_as_entries, tensorCode_as_entries] at h
  obtain ⟨hl, hrest⟩ := tensor_encNat_prefix_unique l l' _ _ h
  obtain ⟨hm, hrest⟩ := tensor_encNat_prefix_unique m m' _ _ hrest
  obtain ⟨hn, _⟩ := tensor_encNat_prefix_unique n n' _ _ hrest
  exact ⟨hl, hm, hn⟩

theorem tensorCode_unique {l m n l' m' n' : ℕ}
    (A : Fin l → Fin m → Fin n → ℚ) (B : Fin l' → Fin m' → Fin n' → ℚ)
    (h : TensorNP.Bilinear.tensorCode A = TensorNP.Bilinear.tensorCode B) :
    l = l' ∧ m = m' ∧ n = n' ∧ HEq A B := by
  obtain ⟨hl, hm, hn⟩ := tensorCode_dimensions_unique A B h
  subst l'
  subst m'
  subst n'
  exact ⟨rfl, rfl, rfl, heq_of_eq (tensorCode_injective_fixed h)⟩

theorem empty_not_tbfLang (F : Type*) [Field F] : ([] : List BSym) ∉ TensorNP.Bilinear.tbfLang F := by
  rintro ⟨l, m, n, A, _, hcode⟩
  rw [tensorCode_as_entries] at hcode
  have hnil : encNat l = [] := (List.append_eq_nil_iff.mp hcode.symm).1
  exact encNat_not_nil l hnil

end TensorNP.BilinearCode

                                                              
                                                                
                                                     
                                                     


namespace TensorNP.BilinearEncoder
open TensorNP.Bilinear

-- Source audit: extracted exact enumeration and reindexing bodies from
-- Work/TensorAGRealCodeBound.lean, independent of its semantic theorem imports.
/-- Row-major candidate pairs, filtered by the strict minor-index condition. -/
def minorPairs (N : ℕ) : List (Fin N × Fin N) :=
  (List.ofFn (finProdFinEquiv.symm : Fin (N * N) → Fin N × Fin N)).filter
    (fun ab ↦ decide (ab.1 < ab.2))

private lemma mem_minorPairs (N : ℕ) (ab : Fin N × Fin N) :
    ab ∈ minorPairs N ↔ ab.1 < ab.2 := by
  simp only [minorPairs, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    apply List.mem_ofFn.mpr
    exact ⟨finProdFinEquiv ab, by simp⟩

private lemma minorPairs_nodup (N : ℕ) : (minorPairs N).Nodup := by
  apply List.Nodup.filter
  apply List.nodup_ofFn_ofInjective
  exact finProdFinEquiv.symm.injective

private def listedMinorEquiv (N : ℕ) : { ab // ab ∈ minorPairs N } ≃ MinorIdx N where
  toFun ab := ⟨ab.val, (mem_minorPairs N ab.val).mp ab.property⟩
  invFun ab := ⟨ab.val, (mem_minorPairs N ab.val).mpr ab.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

private def listToMinor (N : ℕ) : Fin (minorPairs N).length ≃ MinorIdx N :=
  ((minorPairs_nodup N).getEquiv (minorPairs N)).trans (listedMinorEquiv N)

private lemma minor_card (N : ℕ) : Fintype.card (MinorIdx N) = N.choose 2 := by
  classical
  rw [Fintype.card_subtype]
  simpa only [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin N))))

private lemma minorPairs_length (N : ℕ) : (minorPairs N).length = N.choose 2 := by
  have h := Fintype.card_congr (listToMinor N)
  simpa only [Fintype.card_fin, minor_card] using h

/-- Computable finite-list enumeration of the strictly ordered minor indices. -/
def minorEquiv (N : ℕ) : Fin (N.choose 2) ≃ MinorIdx N :=
  (finCongr (minorPairs_length N)).symm.trans (listToMinor N)

private lemma slice_count (v : ℕ) : Fintype.card (SliceIdx v) = v * (2 * v + 5) := by
  classical
  simp only [SliceIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, minor_card,
    Nat.choose_two_right]
  have h : 2 * v + 1 - 1 = 2 * v := by omega
  rw [h]
  have hmul : (2 * v + 1) * (2 * v) = 2 * (v * (2 * v + 1)) := by ring
  rw [hmul]
  simp
  ring

private lemma block_count (v : ℕ) : (2 * v + 1).choose 2 + (3 * v + v) = v * (2 * v + 5) := by
  have h := slice_count v
  simp only [SliceIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, minor_card] at h
  exact h

/-- Explicit list-based enumeration of all the tensor's slice indices. -/
def explicitSliceEquiv (v : ℕ) : Fin (v * (2 * v + 5)) ≃ SliceIdx v :=
  (finCongr (block_count v)).symm.trans
    (finSumFinEquiv.symm.trans
      ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm).trans
        (Equiv.sumCongr (minorEquiv (2 * v + 1))
          (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl _)))))

open Finset TensorNP.Bilinear

private lemma sum2_equiv {I J I' J' R : Type*} [Fintype I] [Fintype J]
    [Fintype I'] [Fintype J'] [AddCommMonoid R]
    (ei : I' ≃ I) (ej : J' ≃ J) (f : I → J → R) :
    (∑ i : I', ∑ j : J', f (ei i) (ej j)) = ∑ i : I, ∑ j : J, f i j := by
  calc
    _ = ∑ i : I', ∑ j : J, f (ei i) j := by
      apply Finset.sum_congr rfl
      intro i _
      exact ej.sum_comp (f (ei i))
    _ = _ := ei.sum_comp (fun i ↦ ∑ j, f i j)

private lemma comp_ne_zero {I I' F : Type*} [Zero F] (e : I' ≃ I)
    {x : I → F} (hx : x ≠ 0) : (fun i ↦ x (e i)) ≠ 0 := by
  intro heq
  apply hx
  funext i
  have hi := congrFun heq (e.symm i)
  simpa using hi

private lemma tbf_reindex_forward {I J K I' J' K' F : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype I'] [Fintype J'] [Fintype K'] [CommRing F]
    (ei : I' ≃ I) (ej : J' ≃ J) (ek : K' ≃ K) (A : I → J → K → F) :
    TBF A → TBF (fun i j k ↦ A (ei i) (ej j) (ek k)) := by
  rintro ⟨u, v, w, hu, hv, hw, h1, h2, h3⟩
  refine ⟨(fun i ↦ u (ei i)), (fun j ↦ v (ej j)), (fun k ↦ w (ek k)),
    comp_ne_zero ei hu, comp_ne_zero ej hv, comp_ne_zero ek hw, ?_, ?_, ?_⟩
  · intro i
    change (∑ j : J', ∑ k : K', A (ei i) (ej j) (ek k) * v (ej j) * w (ek k)) = 0
    rw [sum2_equiv ej ek (fun j k ↦ A (ei i) j k * v j * w k)]
    exact h1 (ei i)
  · intro j
    change (∑ i : I', ∑ k : K', A (ei i) (ej j) (ek k) * u (ei i) * w (ek k)) = 0
    rw [sum2_equiv ei ek (fun i k ↦ A i (ej j) k * u i * w k)]
    exact h2 (ej j)
  · intro k
    change (∑ i : I', ∑ j : J', A (ei i) (ej j) (ek k) * u (ei i) * v (ej j)) = 0
    rw [sum2_equiv ei ej (fun i j ↦ A i j (ek k) * u i * v j)]
    exact h3 (ek k)

theorem tbf_reindex_iff {I J K I' J' K' F : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype I'] [Fintype J'] [Fintype K'] [CommRing F]
    (ei : I' ≃ I) (ej : J' ≃ J) (ek : K' ≃ K) (A : I → J → K → F) :
    TBF A ↔ TBF (fun i j k ↦ A (ei i) (ej j) (ek k)) := by
  constructor
  · exact tbf_reindex_forward ei ej ek A
  · intro h
    have hh := tbf_reindex_forward ei.symm ej.symm ek.symm _ h
    simpa using hh


end TensorNP.BilinearEncoder

                                                         
                                                      

                                                              

                                       

                                          

                                                         

                                         


namespace TensorNP.BilinearEncoder
open TensorNP.Bilinear

-- Actual order-proof bodies adapted from Work/TensorMinorEmissionOrder.lean
-- and Work/TensorAGActualMinorOrder.lean; no runtime inverse index is needed.
theorem minorPairs_length_le (N : ℕ) : (minorPairs N).length ≤ N * N := by
  simpa only [minorPairs, List.length_ofFn] using
    (List.length_filter_le (fun ab : Fin N × Fin N => decide (ab.1 < ab.2))
      (List.ofFn (finProdFinEquiv.symm : Fin (N * N) → Fin N × Fin N)))

theorem minorEquiv_order (N : ℕ) :
    List.ofFn (fun k : Fin (N.choose 2) => (minorEquiv N k).val) = minorPairs N := by
  apply List.ext_getElem
  · simpa [minorPairs_length]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    simp [minorEquiv, listToMinor, listedMinorEquiv, List.Nodup.getEquiv]

private theorem sumSymm_castLE {m n : ℕ} (i : Fin m) :
    finSumFinEquiv.symm (Fin.castLE (Nat.le_add_right m n) i) = Sum.inl i := by
  simpa [Fin.castAdd] using (finSumFinEquiv_symm_apply_castAdd (n := n) i)

theorem explicitSliceEquiv_order (v : ℕ) :
    List.ofFn (explicitSliceEquiv v) =
      List.ofFn (fun k : Fin ((2 * v + 1).choose 2) => Sum.inl (minorEquiv (2 * v + 1) k)) ++
      List.ofFn (fun k : Fin (3 * v) => Sum.inr (Sum.inl (finProdFinEquiv.symm k))) ++
      List.ofFn (fun k : Fin v => Sum.inr (Sum.inr k)) := by
  rw [List.ofFn_congr (block_count v).symm (explicitSliceEquiv v)]
  simp [List.ofFn_add, explicitSliceEquiv, sumSymm_castLE, Function.comp_def]

end TensorNP.BilinearEncoder
end


/- Inlined module: Prefix -/
section
set_option autoImplicit false

open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

structure PrefixResult where
  patternRest : List BSym
  inputRest : List BSym
  matched : ℕ

def prefixResult : List BSym → List BSym → PrefixResult
  | [], input => ⟨[], input, 0⟩
  | a :: pattern, [] => ⟨a :: pattern, [], 0⟩
  | a :: pattern, b :: input =>
      if a = b then
        let r := prefixResult pattern input
        ⟨r.patternRest, r.inputRest, r.matched + 1⟩
      else ⟨a :: pattern, b :: input, 0⟩

def prefixStore (pattern input status : List BSym) : Fin 3 → List BSym :=
  fun k => if k = 0 then pattern else if k = 1 then input else status

def prefixGuard (h : Fin 3 → Option BSym) : Bool :=
  (h 0).isSome && decide (h 0 = h 1)

def prefixPop (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 0 ∨ k = 1 then .pop else .keep

def prefixLoop : StackProg (Fin 3) BSym := .loop prefixGuard (.act prefixPop)

def prefixMark (h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push (if (h 0).isNone then .one else .zero) else .keep

def prefixProg : StackProg (Fin 3) BSym := .seq prefixLoop (.act prefixMark)

theorem prefixPop_step (a b : BSym) (pattern input status : List BSym) :
    StackProg.applyAct prefixPop (prefixStore (a :: pattern) (b :: input) status) =
      prefixStore pattern input status := by
  funext k
  fin_cases k <;> rfl

theorem prefixLoop_exec (pattern input status : List BSym) :
    prefixLoop.Exec (prefixStore pattern input status)
      (prefixStore (prefixResult pattern input).patternRest
        (prefixResult pattern input).inputRest status)
      (3 * (prefixResult pattern input).matched + 1) := by
  induction pattern generalizing input with
  | nil =>
      exact StackProg.Exec.loopFalse (by simp [prefixGuard, prefixStore])
  | cons a pattern ih =>
      cases input with
      | nil =>
          exact StackProg.Exec.loopFalse (by simp [prefixGuard, prefixStore])
      | cons b input =>
          by_cases hab : a = b
          · simp only [prefixResult, if_pos hab]
            convert StackProg.Exec.loopTrue
              (test := prefixGuard) (p := .act prefixPop)
              (s := prefixStore (a :: pattern) (b :: input) status)
              (by simp [prefixGuard, prefixStore, hab])
              (show (StackProg.act prefixPop).Exec
                  (prefixStore (a :: pattern) (b :: input) status)
                  (prefixStore pattern input status) 1 from
                by simpa only [prefixPop_step] using
                  (StackProg.Exec.act prefixPop
                    (prefixStore (a :: pattern) (b :: input) status)))
              (ih input) using 1 <;> first | rfl | omega
          · simp only [prefixResult, if_neg hab]
            exact StackProg.Exec.loopFalse (by simp [prefixGuard, prefixStore, hab])

theorem prefixMark_step (pattern input status : List BSym) :
    StackProg.applyAct prefixMark (prefixStore pattern input status) =
      prefixStore pattern input ((if pattern = [] then BSym.one else .zero) :: status) := by
  cases pattern <;> funext k <;> fin_cases k <;> rfl

theorem prefixProg_exec (pattern input status : List BSym) :
    prefixProg.Exec (prefixStore pattern input status)
      (prefixStore (prefixResult pattern input).patternRest
        (prefixResult pattern input).inputRest
        ((if (prefixResult pattern input).patternRest = [] then BSym.one else .zero) :: status))
      (3 * (prefixResult pattern input).matched + 3) := by
  exact StackProg.Exec.seq (prefixLoop_exec pattern input status)
    (show (StackProg.act prefixMark).Exec
      (prefixStore (prefixResult pattern input).patternRest
        (prefixResult pattern input).inputRest status)
      (prefixStore (prefixResult pattern input).patternRest
        (prefixResult pattern input).inputRest
        ((if (prefixResult pattern input).patternRest = [] then BSym.one else .zero) :: status)) 1 from
      by simpa only [prefixMark_step] using
        (StackProg.Exec.act prefixMark
          (prefixStore (prefixResult pattern input).patternRest
            (prefixResult pattern input).inputRest status)))

theorem prefixResult_matched_le (pattern input : List BSym) :
    (prefixResult pattern input).matched ≤ pattern.length := by
  induction pattern generalizing input with
  | nil => simp [prefixResult]
  | cons a pattern ih =>
      cases input with
      | nil => simp [prefixResult]
      | cons b input =>
          by_cases hab : a = b
          · simpa [prefixResult, hab] using Nat.succ_le_succ (ih input)
          · simp [prefixResult, hab]

theorem prefixResult_append (pattern tail : List BSym) :
    prefixResult pattern (pattern ++ tail) = ⟨[], tail, pattern.length⟩ := by
  induction pattern with
  | nil => rfl
  | cons a pattern ih => simp [prefixResult, ih]

theorem prefixResult_sound (pattern input : List BSym)
    (h : (prefixResult pattern input).patternRest = []) :
    input = pattern ++ (prefixResult pattern input).inputRest := by
  induction pattern generalizing input with
  | nil => rfl
  | cons a pattern ih =>
      cases input with
      | nil => simp [prefixResult] at h
      | cons b input =>
          by_cases hab : a = b
          · subst b
            simpa [prefixResult] using congrArg (List.cons a) (ih input (by simpa [prefixResult] using h))
          · simp [prefixResult, hab] at h

theorem prefixResult_success_iff (pattern input : List BSym) :
    (prefixResult pattern input).patternRest = [] ↔ ∃ tail, input = pattern ++ tail := by
  constructor
  · intro h
    exact ⟨_, prefixResult_sound pattern input h⟩
  · rintro ⟨tail, rfl⟩
    rw [prefixResult_append]

theorem prefixProg_complete (pattern tail status : List BSym) :
    prefixProg.Exec (prefixStore pattern (pattern ++ tail) status)
      (prefixStore [] tail (BSym.one :: status)) (3 * pattern.length + 3) := by
  simpa [prefixResult_append] using
    (prefixProg_exec pattern (pattern ++ tail) status)

theorem prefixResult_matched_le_input (pattern input : List BSym) :
    (prefixResult pattern input).matched ≤ input.length := by
  induction pattern generalizing input with
  | nil => simp [prefixResult]
  | cons a pattern ih =>
      cases input with
      | nil => simp [prefixResult]
      | cons b input =>
          by_cases hab : a = b
          · simpa [prefixResult, hab] using Nat.succ_le_succ (ih input)
          · simp [prefixResult, hab]

end TensorNP.Encoder
end


/- Inlined module: HeaderSearch -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

/-- A successful search retains the dimension, unused fuel, and suffix. -/
structure HeaderResult where
  dimension : ℕ
  fuel : ℕ
  suffix : List BSym
  found : Bool

/-- At most fuel candidates, starting at dimension n. -/
def boundedHeader : ℕ → ℕ → List BSym → HeaderResult
  | n, 0, _ => ⟨n, 0, [], false⟩
  | n, fuel + 1, input =>
      let r := prefixResult (encNat n) input
      if r.patternRest = [] then ⟨n, fuel + 1, r.inputRest, true⟩
      else boundedHeader (n + 1) fuel input

/-- Writer ports 0--4; original input5, working suffix6, fuel7, status8; scratch9--11. -/
def headerStore (n fuel : ℕ) (input suffix : List BSym) (found : Bool) : Fin 12 → List BSym :=
  fun k => if k = 0 then List.replicate n .one else if k = 5 then input
    else if k = 6 then suffix else if k = 7 then List.replicate fuel .one
    else if k = 8 then (if found then [.one] else []) else []

def headerResultStore (r : HeaderResult) (input : List BSym) : Fin 12 → List BSym :=
  headerStore r.dimension r.fuel input r.suffix r.found

def headerGuard (h : Fin 12 → Option BSym) : Bool :=
  (h 7).isSome && !(h 8 == some BSym.one)

def headerStepResult (n fuel : ℕ) (input : List BSym) : Fin 12 → List BSym :=
  let r := prefixResult (encNat n) input
  if r.patternRest = [] then headerStore n fuel input r.inputRest true
  else headerStore (n+1) (fuel-1) input [] false

theorem headerGuard_searching (n fuel : ℕ) (input : List BSym) :
    headerGuard (fun k => (headerStore n (fuel+1) input [] false k).head?) = true := by
  simp [headerGuard, headerStore, List.replicate_succ]

theorem headerGuard_found (n fuel : ℕ) (input suffix : List BSym) :
    headerGuard (fun k => (headerStore n fuel input suffix true k).head?) = false := by
  simp [headerGuard, headerStore]

/-- A bounded candidate step yields a bounded complete search, even on malformed inputs. -/
theorem headerLoop_exec (body : StackProg (Fin 12) BSym) (B : ℕ) (input : List BSym)
    (hstep : ∀ n fuel : ℕ, 0 < fuel → n + fuel ≤ input.length + 1 →
      ∃ steps, body.Exec (headerStore n fuel input [] false)
        (headerStepResult n fuel input) steps ∧ steps ≤ B) :
    ∀ fuel n : ℕ, n + fuel ≤ input.length + 1 →
      ∃ steps, (StackProg.loop headerGuard body).Exec
        (headerStore n fuel input [] false) (headerResultStore (boundedHeader n fuel input) input) steps ∧
        steps ≤ fuel * (B + 2) + 1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro n _
      refine ⟨1, ?_, by simp⟩
      exact StackProg.Exec.loopFalse (by simp [headerGuard, headerStore])
  | succ fuel ih =>
      intro n hbudget
      obtain ⟨m, hm, hmB⟩ := hstep n (fuel+1) (by omega) hbudget
      by_cases hmatch : (prefixResult (encNat n) input).patternRest = []
      · have hm' : body.Exec (headerStore n (fuel+1) input [] false)
            (headerStore n (fuel+1) input (prefixResult (encNat n) input).inputRest true) m := by
          simpa [headerStepResult, hmatch] using hm
        have hstop : (StackProg.loop headerGuard body).Exec
            (headerStore n (fuel+1) input (prefixResult (encNat n) input).inputRest true)
            (headerStore n (fuel+1) input (prefixResult (encNat n) input).inputRest true) 1 :=
          StackProg.Exec.loopFalse (headerGuard_found _ _ _ _)
        refine ⟨1 + m + 1 + 1, ?_, ?_⟩
        · simpa [boundedHeader, hmatch, headerResultStore] using
            (StackProg.Exec.loopTrue (headerGuard_searching n fuel input) hm' hstop)
        · nlinarith
      · have hm' : body.Exec (headerStore n (fuel+1) input [] false)
            (headerStore (n+1) fuel input [] false) m := by
          simpa [headerStepResult, hmatch] using hm
        obtain ⟨r, hr, hrB⟩ := ih (n+1) (by omega)
        refine ⟨1 + m + 1 + r, ?_, ?_⟩
        · simpa [boundedHeader, hmatch] using
            (StackProg.Exec.loopTrue (headerGuard_searching n fuel input) hm' hr)
        · nlinarith

theorem boundedHeader_sound (n fuel : ℕ) (input : List BSym)
    (hfound : (boundedHeader n fuel input).found = true) :
    n ≤ (boundedHeader n fuel input).dimension ∧
      (boundedHeader n fuel input).dimension < n + fuel ∧
      input = encNat (boundedHeader n fuel input).dimension ++ (boundedHeader n fuel input).suffix := by
  induction fuel generalizing n with
  | zero => simp [boundedHeader] at hfound
  | succ fuel ih =>
      by_cases hmatch : (prefixResult (encNat n) input).patternRest = []
      · simp only [boundedHeader, if_pos hmatch]
        exact ⟨le_rfl, by omega, prefixResult_sound _ _ hmatch⟩
      · have hfound' : (boundedHeader (n+1) fuel input).found = true := by
          simpa [boundedHeader, hmatch] using hfound
        obtain ⟨hlo, hhi, heq⟩ := ih (n+1) hfound'
        simp only [boundedHeader, if_neg hmatch]
        exact ⟨by omega, by omega, heq⟩

theorem boundedHeader_complete (n fuel v : ℕ) (input tail : List BSym)
    (hvlo : n ≤ v) (hvhi : v < n + fuel) (hinput : input = encNat v ++ tail) :
    (boundedHeader n fuel input).found = true := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
      by_cases hmatch : (prefixResult (encNat n) input).patternRest = []
      · simp [boundedHeader, hmatch]
      · have hvne : v ≠ n := by
          intro heq
          subst v
          exact hmatch ((prefixResult_success_iff _ _).mpr ⟨tail, hinput⟩)
        simpa [boundedHeader, hmatch] using ih (n+1) (by omega) (by omega)

end TensorNP.Encoder
end


/- Inlined module: HeaderCodes -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def digitValue : List BSym → ℕ
  | [] => 0
  | b :: rest => 2 * digitValue rest + if b = .one then 1 else 0

theorem digitValue_bits (n : ℕ) :
    digitValue ((Nat.bits n).map (fun b => if b then BSym.one else .zero)) = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
      rw [Nat.bits_append_bit n b h]
      cases b <;> simp [digitValue, ih, Nat.bit]

theorem terminated_prefix_unique (xs ys s t : List BSym)
    (hx : ∀ a ∈ xs, a ≠ BSym.sep) (hy : ∀ a ∈ ys, a ≠ BSym.sep)
    (h : xs ++ BSym.sep :: s = ys ++ BSym.sep :: t) : xs = ys ∧ s = t := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact ⟨rfl, (List.cons.inj h).2⟩
      | cons b ys =>
          exact False.elim ((hy b (by simp)) (List.cons.inj h).1.symm)
  | cons a xs ih =>
      cases ys with
      | nil => exact False.elim ((hx a (by simp)) (List.cons.inj h).1)
      | cons b ys =>
          have hab := (List.cons.inj h).1
          subst b
          obtain ⟨hxs, hst⟩ := ih ys
            (fun b hb => hx b (by simp [hb]))
            (fun b hb => hy b (by simp [hb])) (List.cons.inj h).2
          exact ⟨congrArg (List.cons a) hxs, hst⟩

theorem encNat_prefix_unique (n m : ℕ) (s t : List BSym)
    (h : encNat n ++ s = encNat m ++ t) : n = m ∧ s = t := by
  have hdigit : ∀ n : ℕ, ∀ a ∈ (Nat.bits n).map (fun b => if b then BSym.one else .zero),
      a ≠ BSym.sep := by
    intro n a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    cases b <;> decide
  obtain ⟨hd, hst⟩ := terminated_prefix_unique
    ((Nat.bits n).map (fun b => if b then BSym.one else .zero))
    ((Nat.bits m).map (fun b => if b then BSym.one else .zero)) s t
    (hdigit n) (hdigit m) (by simpa [encNat, List.append_assoc] using h)
  exact ⟨by simpa only [digitValue_bits] using congrArg digitValue hd, hst⟩

theorem boundedHeader_canonical (n fuel v : ℕ) (input tail : List BSym)
    (hvlo : n ≤ v) (hvhi : v < n + fuel) (hinput : input = encNat v ++ tail) :
    (boundedHeader n fuel input).dimension = v ∧
      (boundedHeader n fuel input).suffix = tail ∧
      (boundedHeader n fuel input).found = true := by
  have hf := boundedHeader_complete n fuel v input tail hvlo hvhi hinput
  have hs := boundedHeader_sound n fuel input hf
  have hu := encNat_prefix_unique _ _ _ _ (hs.2.2.symm.trans hinput)
  exact ⟨hu.1, hu.2, hf⟩

end TensorNP.Encoder
end


/- Inlined module: GraphCode -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

theorem encNats_length_ge (xs : List ℕ) : xs.length ≤ (encNats xs).length := by
  induction xs with
  | nil => simp [encNats]
  | cons n xs ih =>
      simp only [List.length_cons, encNats, List.flatMap_cons, List.length_append,
        encNat, List.length_map] at *
      omega

theorem graphCode_dimension_sq_le {v : ℕ} (G : SimpleGraph (Fin v)) :
    v * v + 1 ≤ (TensorNP.Eigen.graphCode G).length := by
  classical
  have h := encNats_length_ge ([v] ++ (List.ofFn fun i : Fin v =>
    List.ofFn fun j : Fin v => if G.Adj i j then 1 else 0).flatten)
  simpa [TensorNP.Eigen.graphCode, List.length_flatten, Function.comp_def, List.sum_ofFn] using h

theorem graphCode_dimension_le {v : ℕ} (G : SimpleGraph (Fin v)) :
    v ≤ (TensorNP.Eigen.graphCode G).length := by
  have h := graphCode_dimension_sq_le G
  have hv := Nat.le_mul_self v
  omega

open Classical in
noncomputable def graphTail {v : ℕ} (G : SimpleGraph (Fin v)) : List BSym :=
  encNats ((List.ofFn fun i : Fin v =>
    List.ofFn fun j : Fin v => if G.Adj i j then 1 else 0).flatten)

theorem graphCode_header {v : ℕ} (G : SimpleGraph (Fin v)) :
    TensorNP.Eigen.graphCode G = encNat v ++ graphTail G := by
  classical
  simp [TensorNP.Eigen.graphCode, graphTail, encNats]

theorem boundedHeader_graphCode {v : ℕ} (G : SimpleGraph (Fin v)) :
    let w := TensorNP.Eigen.graphCode G
    (boundedHeader 0 (w.length+1) w).dimension = v ∧
      (boundedHeader 0 (w.length+1) w).suffix = graphTail G ∧
      (boundedHeader 0 (w.length+1) w).found = true := by
  exact boundedHeader_canonical _ _ v _ _ (Nat.zero_le _) (by
    have h := graphCode_dimension_le G
    omega) (graphCode_header G)

end TensorNP.Encoder
end


/- Inlined module: Bits -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.Encoder

def bitCode (b : Bool) : List BSym := if b then [.one, .sep] else [.sep]

def bitsCode (bs : List Bool) : List BSym := bs.flatMap bitCode

def parseBits : ℕ → List BSym → Option (List Bool × List BSym)
  | 0, input => some ([], input)
  | k + 1, .sep :: rest => (parseBits k rest).map fun p => (false :: p.1, p.2)
  | k + 1, .one :: .sep :: rest => (parseBits k rest).map fun p => (true :: p.1, p.2)
  | _ + 1, _ => none

theorem parseBits_sound (count : ℕ) (input : List BSym) (bs : List Bool)
    (tail : List BSym) (h : parseBits count input = some (bs, tail)) :
    bs.length = count ∧ input = bitsCode bs ++ tail := by
  induction count generalizing input bs tail with
  | zero =>
      simp [parseBits] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [bitsCode]
  | succ count ih =>
      cases input with
      | nil => simp [parseBits] at h
      | cons a rest =>
          cases a with
          | zero => simp [parseBits] at h
          | minus => simp [parseBits] at h
          | sep =>
              cases hp : parseBits count rest with
              | none => simp [parseBits, hp] at h
              | some p =>
                  rcases p with ⟨bs', tail'⟩
                  simp [parseBits, hp] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨hlen, hinput⟩ := ih rest bs' tail' hp
                  simp [bitsCode, bitCode, hlen, hinput]
          | one =>
              cases rest with
              | nil => simp [parseBits] at h
              | cons a rest =>
                  cases a with
                  | zero => simp [parseBits] at h
                  | one => simp [parseBits] at h
                  | minus => simp [parseBits] at h
                  | sep =>
                      cases hp : parseBits count rest with
                      | none => simp [parseBits, hp] at h
                      | some p =>
                          rcases p with ⟨bs', tail'⟩
                          simp [parseBits, hp] at h
                          obtain ⟨rfl, rfl⟩ := h
                          obtain ⟨hlen, hinput⟩ := ih rest bs' tail' hp
                          simp [bitsCode, bitCode, hlen, hinput]

theorem bitCode_eq_encNat (b : Bool) : bitCode b = encNat (if b then 1 else 0) := by
  cases b <;> decide

theorem parseBits_complete (bs : List Bool) (tail : List BSym) :
    parseBits bs.length (bitsCode bs ++ tail) = some (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [bitsCode] at ih
      cases b <;> simp [bitsCode, bitCode, parseBits, ih]

theorem bitsCode_length_bounds (bs : List Bool) :
    bs.length ≤ (bitsCode bs).length ∧ (bitsCode bs).length ≤ 2 * bs.length := by
  induction bs with
  | nil => simp [bitsCode]
  | cons b bs ih =>
      cases b <;> simp [bitsCode, bitCode] at * <;> omega

theorem bitsCode_eq_encNats (bs : List Bool) :
    bitsCode bs = encNats (bs.map (fun b => if b then 1 else 0)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [bitsCode, encNats] at ih
      simp [bitsCode, encNats, bitCode_eq_encNat, ih]

end TensorNP.Encoder
end


/- Inlined module: GraphMatrix -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def flattenMatrix {n : ℕ} (f : Fin n → Fin n → Bool) : List Bool :=
  (List.ofFn fun i => List.ofFn (f i)).flatten

theorem flattenMatrix_ofFn {n : ℕ} (f : Fin n → Fin n → Bool) :
    flattenMatrix f = List.ofFn (fun k : Fin (n*n) =>
      f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
  rw [List.ofFn_mul']
  unfold flattenMatrix
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have heq : (⟨n * i.val + j.val, by nlinarith [Nat.mul_le_mul_left n i.isLt, j.isLt]⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm]
  rw [heq, Equiv.symm_apply_apply]

theorem flattenMatrix_getD {n : ℕ} (f : Fin n → Fin n → Bool) (i j : Fin n) :
    (flattenMatrix f).getD (i.val*n+j.val) false = f i j := by
  rw [flattenMatrix_ofFn]
  have hidx : i.val*n+j.val < n*n := by
    nlinarith [Nat.mul_le_mul_left n i.isLt, j.isLt]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hidx), List.getElem_ofFn]
  have heq : (⟨i.val*n+j.val, hidx⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [heq, Equiv.symm_apply_apply]

theorem flattenMatrix_length {n : ℕ} (f : Fin n → Fin n → Bool) :
    (flattenMatrix f).length = n*n := by
  rw [flattenMatrix_ofFn, List.length_ofFn]

def ValidMatrix (n : ℕ) (bs : List Bool) : Prop :=
  bs.length = n*n ∧
    (∀ i : Fin n, bs.getD (i.val*n+i.val) false = false) ∧
    ∀ i j : Fin n, bs.getD (i.val*n+j.val) false = bs.getD (j.val*n+i.val) false

def matrixGraph (n : ℕ) (bs : List Bool) (h : ValidMatrix n bs) : SimpleGraph (Fin n) where
  Adj i j := bs.getD (i.val*n+j.val) false = true
  symm := by
    constructor
    intro i j hij
    rw [← h.2.2 i j]
    exact hij
  loopless := by
    constructor
    intro i hi
    exact Bool.noConfusion ((h.2.1 i).symm.trans hi)

noncomputable def graphBits {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool := by
  classical
  exact flattenMatrix (fun i j => decide (G.Adj i j))

theorem graphBits_valid {n : ℕ} (G : SimpleGraph (Fin n)) : ValidMatrix n (graphBits G) := by
  classical
  refine ⟨flattenMatrix_length _, ?_, ?_⟩
  · intro i
    rw [graphBits, flattenMatrix_getD]
    simp
  · intro i j
    rw [graphBits, flattenMatrix_getD, flattenMatrix_getD]
    simp [G.adj_comm]

theorem graphTail_eq_bitsCode {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphTail G = bitsCode (graphBits G) := by
  classical
  rw [bitsCode_eq_encNats]
  simp [graphTail, graphBits, flattenMatrix, List.map_flatten, List.map_ofFn, Function.comp_def]

theorem flattenMatrix_inverse (n : ℕ) (bs : List Bool) (hlen : bs.length = n*n) :
    flattenMatrix (fun i j : Fin n => bs.getD (i.val*n+j.val) false) = bs := by
  rw [flattenMatrix_ofFn]
  apply List.ext_getElem
  · simp only [List.length_ofFn, hlen]
  · intro k hk hk'
    rw [List.getElem_ofFn]
    let q : Fin (n*n) := ⟨k, by simpa only [List.length_ofFn] using hk⟩
    have heq := congrArg Fin.val (finProdFinEquiv.apply_symm_apply q)
    change (finProdFinEquiv.symm q).2.val + n*(finProdFinEquiv.symm q).1.val = k at heq
    have hidx : (finProdFinEquiv.symm q).1.val*n + (finProdFinEquiv.symm q).2.val = k := by
      nlinarith
    change bs.getD ((finProdFinEquiv.symm q).1.val*n + (finProdFinEquiv.symm q).2.val) false = bs[k]
    rw [hidx]
    exact List.getD_eq_getElem bs false hk'

theorem graphBits_matrixGraph (n : ℕ) (bs : List Bool) (h : ValidMatrix n bs) :
    graphBits (matrixGraph n bs h) = bs := by
  classical
  unfold graphBits
  have hf : (fun i j => decide ((matrixGraph n bs h).Adj i j)) =
      (fun i j : Fin n => bs.getD (i.val*n+j.val) false) := by
    funext i j
    simp [matrixGraph]
  rw [hf]
  exact flattenMatrix_inverse n bs h.1

theorem graphCode_matrixGraph (n : ℕ) (bs : List Bool) (h : ValidMatrix n bs) :
    TensorNP.Eigen.graphCode (matrixGraph n bs h) = encNat n ++ bitsCode bs := by
  rw [graphCode_header, graphTail_eq_bitsCode, graphBits_matrixGraph]

theorem canonicalGraph_iff (input : List BSym) :
    (∃ (n : ℕ) (G : SimpleGraph (Fin n)), input = TensorNP.Eigen.graphCode G) ↔
      let r := boundedHeader 0 (input.length+1) input
      r.found = true ∧ ∃ bs : List Bool,
        parseBits (r.dimension*r.dimension) r.suffix = some (bs, []) ∧ ValidMatrix r.dimension bs := by
  constructor
  · rintro ⟨n, G, rfl⟩
    obtain ⟨hdim, hsuffix, hfound⟩ := boundedHeader_graphCode G
    refine ⟨hfound, graphBits G, ?_, ?_⟩
    · rw [hdim, hsuffix, graphTail_eq_bitsCode, ← (graphBits_valid G).1]
      simpa only [List.append_nil] using parseBits_complete (graphBits G) []
    · rw [hdim]
      exact graphBits_valid G
  · rintro ⟨hfound, bs, hparse, hvalid⟩
    have hheader := (boundedHeader_sound 0 (input.length+1) input hfound).2.2
    have hbits := (parseBits_sound _ _ _ _ hparse).2
    refine ⟨_, matrixGraph _ bs hvalid, ?_⟩
    rw [graphCode_matrixGraph]
    simpa only [List.append_nil] using hheader.trans
      (congrArg (fun tail => encNat (boundedHeader 0 (input.length+1) input).dimension ++ tail) hbits)

end TensorNP.Encoder
end


/- Inlined module: GraphInputValid -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.Encoder

instance validMatrixDecidable (n : ℕ) (bs : List Bool) : Decidable (ValidMatrix n bs) := by
  unfold ValidMatrix
  infer_instance

def graphInputValid (input : List BSym) : Bool :=
  let r := boundedHeader 0 (input.length + 1) input
  if r.found then
    match parseBits (r.dimension * r.dimension) r.suffix with
    | none => false
    | some (bs, tail) => decide (tail = [] ∧ ValidMatrix r.dimension bs)
  else false

theorem graphInputValid_iff (input : List BSym) : graphInputValid input = true ↔
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), input = TensorNP.Eigen.graphCode G := by
  rw [canonicalGraph_iff]
  by_cases hf : (boundedHeader 0 (input.length + 1) input).found = true
  · cases hp : parseBits ((boundedHeader 0 (input.length + 1) input).dimension *
        (boundedHeader 0 (input.length + 1) input).dimension)
        (boundedHeader 0 (input.length + 1) input).suffix with
    | none => simp [graphInputValid, hf, hp]
    | some p =>
        rcases p with ⟨bs, tail⟩
        simp [graphInputValid, hf, hp]
  · simp [graphInputValid, hf]

theorem graphInputValid_graphCode {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphInputValid (TensorNP.Eigen.graphCode G) = true := by
  exact (graphInputValid_iff _).2 ⟨n, G, rfl⟩

theorem graphInputValid_invalid (input : List BSym)
    (h : ¬ ∃ (n : ℕ) (G : SimpleGraph (Fin n)), input = TensorNP.Eigen.graphCode G) :
    graphInputValid input = false := by
  cases hv : graphInputValid input with
  | false => rfl
  | true => exact False.elim (h ((graphInputValid_iff input).1 hv))

end TensorNP.Encoder
end


/- Inlined module: FrontLemmas -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

theorem boundedHeader_fuel_le (n fuel : ℕ) (input : List BSym) :
    (boundedHeader n fuel input).fuel ≤ fuel := by
  induction fuel generalizing n with
  | zero => simp [boundedHeader]
  | succ fuel ih =>
      by_cases hmatch : (prefixResult (encNat n) input).patternRest = []
      · simp [boundedHeader, hmatch]
      · simp only [boundedHeader, if_neg hmatch]
        exact Nat.le_trans (ih (n+1)) (Nat.le_succ fuel)

theorem boundedHeader_dimension_le (input : List BSym)
    (hf : (boundedHeader 0 (input.length+1) input).found = true) :
    (boundedHeader 0 (input.length+1) input).dimension ≤ input.length := by
  have h := (boundedHeader_sound 0 (input.length+1) input hf).2.1
  omega

theorem canonical_front_packet {v : ℕ} (G : SimpleGraph (Fin v)) (input : List BSym)
    (hinput : input = TensorNP.Eigen.graphCode G) :
    let r := boundedHeader 0 (input.length+1) input
    r.found = true ∧ r.dimension = v ∧
      parseBits (r.dimension*r.dimension) r.suffix = some (graphBits G, []) ∧
      ValidMatrix r.dimension (graphBits G) := by
  subst input
  obtain ⟨hdim, hsuffix, hfound⟩ := boundedHeader_graphCode G
  refine ⟨hfound, hdim, ?_, ?_⟩
  · rw [hdim, hsuffix, graphTail_eq_bitsCode, ← (graphBits_valid G).1]
    simpa only [List.append_nil] using parseBits_complete (graphBits G) []
  · rw [hdim]
    exact graphBits_valid G

theorem canonical_packet_accept (input : List BSym) (bs : List Bool)
    (hf : (boundedHeader 0 (input.length+1) input).found = true)
    (hp : parseBits ((boundedHeader 0 (input.length+1) input).dimension *
        (boundedHeader 0 (input.length+1) input).dimension)
      (boundedHeader 0 (input.length+1) input).suffix = some (bs, []))
    (hv : ValidMatrix (boundedHeader 0 (input.length+1) input).dimension bs) :
    ∃ (v : ℕ) (G : SimpleGraph (Fin v)), input = TensorNP.Eigen.graphCode G := by
  exact (canonicalGraph_iff input).2 ⟨hf, bs, hp, hv⟩

end TensorNP.Encoder
end


/- Inlined module: Entries -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen Matrix Finset

namespace TensorNP.Encoder

def monomialEntry (row col a b : ℕ) : ℤ := if row = a ∧ col = b then 1 else 0

noncomputable def colorEntryInt {v : ℕ} (G : SimpleGraph (Fin v))
    (p : Fin 4 × Fin v) (a b : Fin (2*v+1)) : ℤ := by
  classical
  exact ![monomialEntry p.2.val (v+p.2.val) a.val b.val - monomialEntry (2*v) (2*v) a.val b.val,
    monomialEntry (v+p.2.val) (2*v) a.val b.val - monomialEntry p.2.val p.2.val a.val b.val,
    monomialEntry p.2.val (2*v) a.val b.val - monomialEntry (v+p.2.val) (v+p.2.val) a.val b.val,
    ∑ j : Fin v, if G.Adj p.2 j then
      monomialEntry p.2.val p.2.val a.val b.val +
      monomialEntry p.2.val j.val a.val b.val + monomialEntry j.val j.val a.val b.val else 0] p.1

theorem monomialEntry_cast (v : ℕ) (row col a b : Fin (2*v+1)) :
    (monomialEntry row.val col.val a.val b.val : ℚ) = Matrix.single row col 1 a b := by
  simp [monomialEntry, Matrix.single_apply, Fin.ext_iff]

theorem colorEntryInt_cast {v : ℕ} (G : SimpleGraph (Fin v))
    (p : Fin 4 × Fin v) (a b : Fin (2*v+1)) :
    (colorEntryInt G p a b : ℚ) = colorEncoding G p a b := by
  classical
  rcases p with ⟨f, i⟩
  fin_cases f <;> simp [colorEntryInt, colorEncoding, monomialEntry,
    Matrix.single_apply, Matrix.sub_apply, Matrix.sum_apply,
    Finset.sum_filter, xVar, yVar, zVar, Fin.ext_iff]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : G.Adj i j <;> simp [hij, Matrix.add_apply, Matrix.single_apply, Fin.ext_iff]

theorem realSplit_map_intCast {m n : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) ℤ)
    (q : Fin (m+m)) (a b : Fin (n+n)) :
    ((realSplit A q a b : ℤ) : ℚ) =
      realSplit (fun k i j => (A k i j : ℚ)) q a b := by
  cases hq : finSumFinEquiv.symm q <;>
    cases ha : finSumFinEquiv.symm a <;>
      cases hb : finSumFinEquiv.symm b <;>
        simp [realSplit, Matrix.reindex_apply, Matrix.fromBlocks, Matrix.neg_apply, hq, ha, hb]
  rfl

theorem padSystem_map_intCast {m n : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) ℤ) (r s : ℕ)
    (q : Fin r) (a b : Fin s) :
    ((padSystem A r s q a b : ℤ) : ℚ) =
      padSystem (fun k i j => (A k i j : ℚ)) r s q a b := by
  unfold padSystem
  split_ifs <;> simp

noncomputable def intColorEncodingFin {v : ℕ} (G : SimpleGraph (Fin v)) :
    Fin (4*v) → Matrix (Fin (2*v+1)) (Fin (2*v+1)) ℤ :=
  fun q a b => colorEntryInt G (finProdFinEquiv.symm q) a b

noncomputable def intColorTensor {v : ℕ} (G : SimpleGraph (Fin v)) :
    Fin (colorSize v) → Fin (colorSize v) → Fin (colorSize v) → ℤ :=
  fun i j k => padSystem (realSplit (intColorEncodingFin G)) (colorSize v) (colorSize v) k i j

theorem intColorTensor_cast {v : ℕ} (G : SimpleGraph (Fin v))
    (i j k : Fin (colorSize v)) :
    (intColorTensor G i j k : ℚ) = colorTensor G i j k := by
  have hA : (fun q a b => (intColorEncodingFin G q a b : ℚ)) = colorEncodingFin G := by
    funext q a b
    exact colorEntryInt_cast G _ a b
  have hB : (fun q a b => ((realSplit (intColorEncodingFin G) q a b : ℤ) : ℚ)) =
      realSplit (colorEncodingFin G) := by
    funext q a b
    rw [realSplit_map_intCast, hA]
  unfold intColorTensor colorTensor squareSystem
  rw [padSystem_map_intCast, hB]

end TensorNP.Encoder
end


/- Inlined module: MatrixCheckSpec -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.Encoder

def symmetryPrefix (n : ℕ) (data : List BSym) (i : ℕ) : ℕ → Bool
  | 0 => true
  | j+1 => decide (data.getD (i*n+j) .zero = data.getD (j*n+i) .zero) && symmetryPrefix n data i j

def matrixCheckPrefix (n : ℕ) (data : List BSym) : ℕ → Bool
  | 0 => true
  | i+1 => decide (data.getD (i*n+i) .zero = BSym.zero) &&
      symmetryPrefix n data i n && matrixCheckPrefix n data i

def checkerStore (n row col : ℕ) (data : List BSym) (good : Bool) : Fin 12 → List BSym :=
  fun k => if k = 0 then data else if k = 1 then List.replicate n .one
    else if k = 2 then List.replicate row .one else if k = 3 then List.replicate col .one
    else if k = 8 then (if good then [] else [.zero]) else []

end TensorNP.Encoder
end


/- Inlined module: BitMachine -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def boolSym (b : Bool) : BSym := if b then .one else .zero

def bitParserStore (input fuel data status : List BSym) : Fin 4 → List BSym :=
  fun k => if k = 0 then input else if k = 1 then fuel else if k = 2 then data else status

def bitGuard (h : Fin 4 → Option BSym) : Bool := (h 1).isSome && (h 3).isNone
def bitIsSep (h : Fin 4 → Option BSym) : Bool := h 0 == some .sep
def bitIsOne (h : Fin 4 → Option BSym) : Bool := h 0 == some .one
def bitStatusEmpty (h : Fin 4 → Option BSym) : Bool := (h 3).isNone

def bitTake (b : BSym) (_ : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else if k = 1 then .pop else if k = 2 then .push b else .keep
def bitPop (_ : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else .keep
def bitMark (b : BSym) (_ : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 3 then .push b else .keep

def bitBody : StackProg (Fin 4) BSym :=
  .branch bitIsSep (.act (bitTake .zero))
    (.branch bitIsOne
      (.seq (.act bitPop) (.branch bitIsSep (.act (bitTake .one)) (.act (bitMark .zero))))
      (.act (bitMark .zero)))

def bitLoop : StackProg (Fin 4) BSym := .loop bitGuard bitBody

def bitProgram : StackProg (Fin 4) BSym :=
  .seq bitLoop (.branch bitStatusEmpty (.act (bitMark .one)) (.act (fun _ _ => .keep)))

lemma bitTake_apply (b a : BSym) (i f d st : List BSym) :
    StackProg.applyAct (bitTake b) (bitParserStore (a :: i) (.one :: f) d st) =
      bitParserStore i f (b :: d) st := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, bitTake, bitParserStore, StackAct.apply]

lemma bitPop_apply (a : BSym) (i f d st : List BSym) :
    StackProg.applyAct bitPop (bitParserStore (a :: i) f d st) = bitParserStore i f d st := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, bitPop, bitParserStore, StackAct.apply]

lemma bitMark_apply (b : BSym) (i f d st : List BSym) :
    StackProg.applyAct (bitMark b) (bitParserStore i f d st) =
      bitParserStore i f d (b :: st) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, bitMark, bitParserStore, StackAct.apply]

lemma bitKeep_apply (s : Fin 4 → List BSym) :
    StackProg.applyAct (fun _ _ => .keep) s = s := by
  funext k
  rfl

lemma bitBody_sep (i f d : List BSym) :
    bitBody.Exec (bitParserStore (.sep :: i) (.one :: f) d [])
      (bitParserStore i f (.zero :: d) []) 2 := by
  have ha : (StackProg.act (bitTake .zero)).Exec
      (bitParserStore (.sep :: i) (.one :: f) d [])
      (bitParserStore i f (.zero :: d) []) 1 := by
    simpa only [bitTake_apply] using StackProg.Exec.act (bitTake .zero)
      (bitParserStore (.sep :: i) (.one :: f) d [])
  exact StackProg.Exec.branchTrue (by simp [bitIsSep, bitParserStore]) ha

lemma bitBody_one (i f d : List BSym) :
    bitBody.Exec (bitParserStore (.one :: .sep :: i) (.one :: f) d [])
      (bitParserStore i f (.one :: d) []) 6 := by
  have hp : (StackProg.act bitPop).Exec
      (bitParserStore (.one :: .sep :: i) (.one :: f) d [])
      (bitParserStore (.sep :: i) (.one :: f) d []) 1 := by
    simpa only [bitPop_apply] using StackProg.Exec.act bitPop
      (bitParserStore (.one :: .sep :: i) (.one :: f) d [])
  have ht : (StackProg.act (bitTake .one)).Exec
      (bitParserStore (.sep :: i) (.one :: f) d [])
      (bitParserStore i f (.one :: d) []) 1 := by
    simpa only [bitTake_apply] using StackProg.Exec.act (bitTake .one)
      (bitParserStore (.sep :: i) (.one :: f) d [])
  have hb := StackProg.Exec.branchTrue (test := bitIsSep) (q := .act (bitMark .zero))
    (by simp [bitIsSep, bitParserStore]) ht
  have hs := StackProg.Exec.seq hp hb
  exact StackProg.Exec.branchFalse (by simp [bitIsSep, bitParserStore])
    (StackProg.Exec.branchTrue (by simp [bitIsOne, bitParserStore]) hs)

lemma bitBody_bad (i f d : List BSym) (hs : i.head? ≠ some .sep)
    (ho : i.head? ≠ some .one) :
    bitBody.Exec (bitParserStore i (.one :: f) d [])
      (bitParserStore i (.one :: f) d [.zero]) 3 := by
  have ha : (StackProg.act (bitMark .zero)).Exec
      (bitParserStore i (.one :: f) d []) (bitParserStore i (.one :: f) d [.zero]) 1 := by
    simpa only [bitMark_apply] using StackProg.Exec.act (bitMark .zero)
      (bitParserStore i (.one :: f) d [])
  exact StackProg.Exec.branchFalse (by simp [bitIsSep, bitParserStore, hs])
    (StackProg.Exec.branchFalse (by simp [bitIsOne, bitParserStore, ho]) ha)

lemma bitBody_one_bad (i f d : List BSym) (hs : i.head? ≠ some .sep) :
    bitBody.Exec (bitParserStore (.one :: i) (.one :: f) d [])
      (bitParserStore i (.one :: f) d [.zero]) 6 := by
  have hp : (StackProg.act bitPop).Exec (bitParserStore (.one :: i) (.one :: f) d [])
      (bitParserStore i (.one :: f) d []) 1 := by
    simpa only [bitPop_apply] using StackProg.Exec.act bitPop
      (bitParserStore (.one :: i) (.one :: f) d [])
  have ha : (StackProg.act (bitMark .zero)).Exec
      (bitParserStore i (.one :: f) d []) (bitParserStore i (.one :: f) d [.zero]) 1 := by
    simpa only [bitMark_apply] using StackProg.Exec.act (bitMark .zero)
      (bitParserStore i (.one :: f) d [])
  have hb := StackProg.Exec.branchFalse (test := bitIsSep) (p := .act (bitTake .one))
    (by simp [bitIsSep, bitParserStore, hs]) ha
  have hh := StackProg.Exec.seq hp hb
  exact StackProg.Exec.branchFalse (by simp [bitIsSep, bitParserStore])
    (StackProg.Exec.branchTrue (by simp [bitIsOne, bitParserStore]) hh)

def bitOutcome (r : Option (List Bool × List BSym)) (d : List BSym)
    (s : Fin 4 → List BSym) : Prop :=
  match r with
  | some (bs, tail) => s = bitParserStore tail [] ((bs.map boolSym).reverse ++ d) []
  | none => s 3 = [.zero]

def bitLoopSpec (count : ℕ) (input d : List BSym) : Prop :=
  ∃ s steps, bitLoop.Exec (bitParserStore input (List.replicate count .one) d []) s steps ∧
    steps ≤ 8 * count + 1 ∧ bitOutcome (parseBits count input) d s

lemma bitLoop_step (count : ℕ) (input d : List BSym) (b : Bool)
    (ih : bitLoopSpec count input (boolSym b :: d)) :
    bitLoopSpec (count + 1) (bitCode b ++ input) d := by
  obtain ⟨s, n, he, hn, hr⟩ := ih
  have hbody : bitBody.Exec
      (bitParserStore (bitCode b ++ input) (.one :: List.replicate count .one) d [])
      (bitParserStore input (List.replicate count .one) (boolSym b :: d) [])
      (if b then 6 else 2) := by
    cases b <;> simp [bitCode, boolSym, bitBody_sep, bitBody_one]
  have hg : bitGuard (fun k =>
      (bitParserStore (bitCode b ++ input) (.one :: List.replicate count .one) d [] k).head?) = true := by
    simp [bitGuard, bitParserStore]
  have hex := StackProg.Exec.loopTrue hg hbody he
  refine ⟨s, 1 + (if b then 6 else 2) + 1 + n, ?_, ?_, ?_⟩
  · simpa [bitLoop, List.replicate_succ] using hex
  · cases b <;> simp_all <;> omega
  · cases hp : parseBits count input with
    | none =>
        cases b <;> simpa [bitOutcome, bitCode, parseBits, hp] using hr
    | some p =>
        rcases p with ⟨bs, tail⟩
        cases b <;> simpa [bitOutcome, bitCode, parseBits, hp, boolSym, List.reverse_cons,
          List.append_assoc] using hr

lemma bitLoop_bad (count : ℕ) (input d : List BSym)
    (hs : input.head? ≠ some .sep) (ho : input.head? ≠ some .one)
    (hparse : parseBits (count + 1) input = none) : bitLoopSpec (count + 1) input d := by
  have hf : bitLoop.Exec (bitParserStore input (.one :: List.replicate count .one) d [.zero])
      (bitParserStore input (.one :: List.replicate count .one) d [.zero]) 1 := by
    apply StackProg.Exec.loopFalse
    simp [bitGuard, bitParserStore]
  have he := StackProg.Exec.loopTrue (test := bitGuard)
    (by simp [bitGuard, bitParserStore]) (bitBody_bad input _ d hs ho) hf
  refine ⟨bitParserStore input (.one :: List.replicate count .one) d [.zero], 6, ?_, by omega, ?_⟩
  · simpa [bitLoop, List.replicate_succ] using he
  · simp [bitOutcome, hparse, bitParserStore]

lemma bitLoop_one_bad (count : ℕ) (input d : List BSym)
    (hs : input.head? ≠ some .sep)
    (hparse : parseBits (count + 1) (.one :: input) = none) :
    bitLoopSpec (count + 1) (.one :: input) d := by
  have hf : bitLoop.Exec (bitParserStore input (.one :: List.replicate count .one) d [.zero])
      (bitParserStore input (.one :: List.replicate count .one) d [.zero]) 1 := by
    apply StackProg.Exec.loopFalse
    simp [bitGuard, bitParserStore]
  have he := StackProg.Exec.loopTrue (test := bitGuard)
    (by simp [bitGuard, bitParserStore]) (bitBody_one_bad input _ d hs) hf
  refine ⟨bitParserStore input (.one :: List.replicate count .one) d [.zero], 9, ?_, by omega, ?_⟩
  · simpa [bitLoop, List.replicate_succ] using he
  · simp [bitOutcome, hparse, bitParserStore]

theorem bitLoop_spec (count : ℕ) (input d : List BSym) : bitLoopSpec count input d := by
  induction count generalizing input d with
  | zero =>
      refine ⟨bitParserStore input [] d [], 1, ?_, by simp, ?_⟩
      · apply StackProg.Exec.loopFalse
        simp [bitGuard, bitParserStore]
      · simp [bitOutcome, parseBits]
  | succ count ih =>
      cases input with
      | nil =>
          apply bitLoop_bad count [] d <;> simp [parseBits]
      | cons a input =>
          cases a with
          | zero => apply bitLoop_bad count (.zero :: input) d <;> simp [parseBits]
          | minus => apply bitLoop_bad count (.minus :: input) d <;> simp [parseBits]
          | sep =>
              simpa [bitCode, boolSym] using bitLoop_step count input d false (ih input (.zero :: d))
          | one =>
              cases input with
              | nil => apply bitLoop_one_bad count [] d <;> simp [parseBits]
              | cons a input =>
                  cases a with
                  | zero => apply bitLoop_one_bad count (.zero :: input) d <;> simp [parseBits]
                  | one => apply bitLoop_one_bad count (.one :: input) d <;> simp [parseBits]
                  | minus => apply bitLoop_one_bad count (.minus :: input) d <;> simp [parseBits]
                  | sep =>
                      simpa [bitCode, boolSym] using bitLoop_step count input d true (ih input (.one :: d))

theorem bit_parser_machine : ∃ p : StackProg (Fin 4) BSym,
    ∀ (count : ℕ) (input : List BSym), ∃ (s : Fin 4 → List BSym) (steps : ℕ),
      p.Exec (bitParserStore input (List.replicate count .one) [] []) s steps ∧
      steps ≤ 20 * (count + 1) ∧
      (∀ (bs : List Bool) (tail : List BSym), parseBits count input = some (bs, tail) →
        s = bitParserStore tail [] ((bs.map boolSym).reverse) [.one]) ∧
      (parseBits count input = none → s 3 = [.zero]) := by
  refine ⟨bitProgram, ?_⟩
  intro count input
  obtain ⟨s, n, he, hn, hr⟩ := bitLoop_spec count input []
  cases hp : parseBits count input with
  | none =>
      have hs : s 3 = [.zero] := by simpa [bitOutcome, hp] using hr
      have hk : (StackProg.act (fun _ _ => .keep)).Exec s s 1 := by
        simpa only [bitKeep_apply] using StackProg.Exec.act (fun _ _ => .keep) s
      have hb := StackProg.Exec.branchFalse (test := bitStatusEmpty)
        (p := .act (bitMark .one)) (by simp [bitStatusEmpty, hs]) hk
      have ht := StackProg.Exec.seq he hb
      refine ⟨s, n + 1 + (1 + 1), ?_, by omega, ?_, fun _ => hs⟩
      · exact ht
      · intro bs tail h
        simp at h
  | some p =>
      rcases p with ⟨bs, tail⟩
      have hs : s = bitParserStore tail [] ((bs.map boolSym).reverse) [] := by
        simpa [bitOutcome, hp] using hr
      subst s
      have ha : (StackProg.act (bitMark .one)).Exec
          (bitParserStore tail [] ((bs.map boolSym).reverse) [])
          (bitParserStore tail [] ((bs.map boolSym).reverse) [.one]) 1 := by
        simpa only [bitMark_apply] using StackProg.Exec.act (bitMark .one)
          (bitParserStore tail [] ((bs.map boolSym).reverse) [])
      have hb := StackProg.Exec.branchTrue (test := bitStatusEmpty)
        (q := .act (fun _ _ => .keep)) (by simp [bitStatusEmpty, bitParserStore]) ha
      have ht := StackProg.Exec.seq he hb
      refine ⟨bitParserStore tail [] ((bs.map boolSym).reverse) [.one], n + 1 + (1 + 1), ?_, by omega, ?_, ?_⟩
      · exact ht
      · intro bs' tail' h
        cases h
        rfl
      · intro h
        contradiction

end TensorNP.Encoder
end


/- Inlined module: MatrixCheckModel -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.Encoder

theorem symmetryPrefix_true_iff (n : ℕ) (data : List BSym) (i count : ℕ) :
    symmetryPrefix n data i count = true ↔
    ∀ j : ℕ, j < count → data.getD (i*n+j) .zero = data.getD (j*n+i) .zero := by
  induction count with
  | zero => simp [symmetryPrefix]
  | succ count ih =>
      simp only [symmetryPrefix, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨he, hp⟩ j hj
        by_cases h : j = count
        · simpa [h] using he
        · exact hp j (by omega)
      · intro h
        exact ⟨h count (by omega), fun j hj => h j (by omega)⟩

theorem matrixCheckPrefix_true_iff (n : ℕ) (data : List BSym) (count : ℕ) :
    matrixCheckPrefix n data count = true ↔
    ∀ i : ℕ, i < count → data.getD (i*n+i) .zero = BSym.zero ∧
      ∀ j : ℕ, j < n → data.getD (i*n+j) .zero = data.getD (j*n+i) .zero := by
  induction count with
  | zero => simp [matrixCheckPrefix]
  | succ count ih =>
      simp only [matrixCheckPrefix, Bool.and_eq_true, decide_eq_true_eq,
        symmetryPrefix_true_iff, ih]
      constructor
      · rintro ⟨⟨hd, hs⟩, hp⟩ i hi
        by_cases h : i = count
        · subst i
          exact ⟨hd, hs⟩
        · exact hp i (by omega)
      · intro h
        refine ⟨⟨(h count (by omega)).1, (h count (by omega)).2⟩, ?_⟩
        intro i hi
        exact h i (by omega)

lemma boolSym_injective : Function.Injective boolSym := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolSym]

lemma getD_map_boolSym (bs : List Bool) (k : ℕ) :
    (bs.map boolSym).getD k .zero = boolSym (bs.getD k false) := by
  simpa [boolSym] using (List.getD_map (l := bs) (d := false) (n := k) boolSym)

theorem matrixCheckPrefix_valid (n : ℕ) (bs : List Bool) (hlen : bs.length = n*n) :
    matrixCheckPrefix n (bs.map boolSym) n = true ↔ ValidMatrix n bs := by
  rw [matrixCheckPrefix_true_iff]
  constructor
  · intro h
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      have hd := (h i.val i.isLt).1
      rw [getD_map_boolSym] at hd
      exact boolSym_injective (by simpa [boolSym] using hd)
    · intro i j
      have hs := (h i.val i.isLt).2 j.val j.isLt
      rw [getD_map_boolSym, getD_map_boolSym] at hs
      exact boolSym_injective hs
  · rintro ⟨_, hd, hs⟩ i hi
    let ii : Fin n := ⟨i, hi⟩
    constructor
    · rw [getD_map_boolSym]
      simpa [boolSym] using congrArg boolSym (hd ii)
    · intro j hj
      let jj : Fin n := ⟨j, hj⟩
      rw [getD_map_boolSym, getD_map_boolSym]
      exact congrArg boolSym (hs ii jj)

end TensorNP.Encoder
end


/- Inlined module: RawEntries -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Eigen

namespace TensorNP.Encoder

def naturalMonomial (row col a b : ℕ) : ℕ := if row = a ∧ col = b then 1 else 0

theorem naturalMonomial_cast (row col a b : ℕ) :
    ((naturalMonomial row col a b : ℕ) : ℤ) = monomialEntry row col a b := by
  simp [naturalMonomial, monomialEntry]

def neighborCount (v : ℕ) (data : List BSym) (vertex a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => neighborCount v data vertex a b j +
      if data.getD (vertex*v+j) .zero = .one then
        naturalMonomial vertex vertex a b + naturalMonomial vertex j a b + naturalMonomial j j a b
      else 0

theorem neighborCount_sum (v : ℕ) (data : List BSym) (vertex a b count : ℕ) :
    ((neighborCount v data vertex a b count : ℕ) : ℤ) =
      ∑ j ∈ Finset.range count, if data.getD (vertex*v+j) .zero = .one then
        monomialEntry vertex vertex a b + monomialEntry vertex j a b + monomialEntry j j a b else 0 := by
  induction count with
  | zero => simp [neighborCount]
  | succ count ih => simp [neighborCount, Finset.sum_range_succ, ih, naturalMonomial_cast]

def rawPositiveCount (v : ℕ) (data : List BSym) (family vertex a b : ℕ) : ℕ :=
  if family = 0 then naturalMonomial vertex (v+vertex) a b
  else if family = 1 then naturalMonomial (v+vertex) (2*v) a b
  else if family = 2 then naturalMonomial vertex (2*v) a b
  else if family = 3 then neighborCount v data vertex a b v else 0

def rawNegativeCount (v family vertex a b : ℕ) : ℕ :=
  if family = 0 then naturalMonomial (2*v) (2*v) a b
  else if family = 1 then naturalMonomial vertex vertex a b
  else if family = 2 then naturalMonomial (v+vertex) (v+vertex) a b else 0

def rawColorEntry (v : ℕ) (data : List BSym) (family vertex a b : ℕ) : ℤ :=
  (rawPositiveCount v data family vertex a b : ℤ) - (rawNegativeCount v family vertex a b : ℤ)

noncomputable def graphData {v : ℕ} (G : SimpleGraph (Fin v)) : List BSym :=
  (graphBits G).map boolSym

open Classical in
theorem graphData_getD {v : ℕ} (G : SimpleGraph (Fin v)) (i j : Fin v) :
    (graphData G).getD (i.val*v+j.val) .zero = if G.Adj i j then BSym.one else BSym.zero := by
  classical
  simp only [graphData, getD_map_boolSym, graphBits, flattenMatrix_getD, boolSym, decide_eq_true_eq]

theorem rawColorEntry_graphData {v : ℕ} (G : SimpleGraph (Fin v))
    (p : Fin 4 × Fin v) (a b : Fin (2*v+1)) :
    rawColorEntry v (graphData G) p.1.val p.2.val a.val b.val = colorEntryInt G p a b := by
  classical
  rcases p with ⟨f, i⟩
  fin_cases f <;> simp [rawColorEntry, rawPositiveCount, rawNegativeCount,
    colorEntryInt, naturalMonomial_cast]
  rw [neighborCount_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [graphData_getD]
  by_cases hij : G.Adj i j <;> simp [hij]

end TensorNP.Encoder
end


/- Inlined module: RawTensor -/
section
set_option autoImplicit false
open TensorNP.Eigen Matrix

namespace TensorNP.Encoder

def rawRealSplit (m n : ℕ) (A : ℕ → ℕ → ℕ → ℤ) (q a b : ℕ) : ℤ :=
  if q < m then
    if a < n then (if b < n then A q a b else 0)
    else (if b < n then 0 else -A q (a-n) (b-n))
  else
    if a < n then (if b < n then 0 else A (q-m) a (b-n))
    else (if b < n then A (q-m) (a-n) b else 0)

theorem realSplit_raw {m n : ℕ} (A : ℕ → ℕ → ℕ → ℤ)
    (q : Fin (m+m)) (a b : Fin (n+n)) :
    realSplit (fun (q : Fin m) (a b : Fin n) => A q.val a.val b.val) q a b =
      rawRealSplit m n A q.val a.val b.val := by
  have hsum (l : ℕ) (i : Fin l) :
      finSumFinEquiv.symm (i.addNat l) = Sum.inr i := by
    have hi : i.addNat l = Fin.natAdd l i := by
      apply Fin.ext
      simp [Nat.add_comm]
    rw [hi, finSumFinEquiv_symm_apply_natAdd]
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective q
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
  cases q <;> cases a <;> cases b <;>
    simp [realSplit, rawRealSplit, Matrix.reindex_apply, Matrix.fromBlocks, hsum]
  rfl


def rawPadSystem (m n : ℕ) (A : ℕ → ℕ → ℕ → ℤ) (r q a b : ℕ) : ℤ :=
  if q < m then (if a < n ∧ b < n then A q a b else 0)
  else if q+1 = r then (if n ≤ a ∧ a=b then 1 else 0) else 0

theorem padSystem_raw {m n : ℕ} (A : ℕ → ℕ → ℕ → ℤ) (r s : ℕ)
    (q : Fin r) (a b : Fin s) :
    padSystem (fun (q : Fin m) (a b : Fin n) => A q.val a.val b.val) r s q a b =
      rawPadSystem m n A r q.val a.val b.val := by
  simp [padSystem, rawPadSystem, Fin.ext_iff]

def rawColorMatrix (v : ℕ) (data : List ProjSchedTW.Complexity.BSym) (q a b : ℕ) : ℤ :=
  rawColorEntry v data (q/v) (q%v) a b

theorem rawColorMatrix_graphData {v : ℕ} (G : SimpleGraph (Fin v))
    (q : Fin (4*v)) (a b : Fin (2*v+1)) :
    rawColorMatrix v (graphData G) q.val a.val b.val = intColorEncodingFin G q a b := by
  unfold rawColorMatrix intColorEncodingFin
  simpa [finProdFinEquiv] using rawColorEntry_graphData G (finProdFinEquiv.symm q) a b

def rawTensorEntry (v : ℕ) (data : List ProjSchedTW.Complexity.BSym) (i j k : ℕ) : ℤ :=
  rawPadSystem (4*v+4*v) (2*v+1+(2*v+1))
    (rawRealSplit (4*v) (2*v+1) (rawColorMatrix v data)) (8*v+2) k i j

theorem rawTensorEntry_graphData {v : ℕ} (G : SimpleGraph (Fin v))
    (i j k : Fin (colorSize v)) :
    rawTensorEntry v (graphData G) i.val j.val k.val = intColorTensor G i j k := by
  have hA : (fun (q : Fin (4*v)) (a b : Fin (2*v+1)) =>
      rawColorMatrix v (graphData G) q.val a.val b.val) = intColorEncodingFin G := by
    funext q a b
    exact rawColorMatrix_graphData G q a b
  have hB : (fun (q : Fin (4*v+4*v)) (a b : Fin (2*v+1+(2*v+1))) =>
      rawRealSplit (4*v) (2*v+1) (rawColorMatrix v (graphData G)) q.val a.val b.val) =
      realSplit (intColorEncodingFin G) := by
    funext q a b
    rw [← realSplit_raw, hA]
  have hpad := padSystem_raw (m := 4*v+4*v) (n := 2*v+1+(2*v+1))
    (rawRealSplit (4*v) (2*v+1) (rawColorMatrix v (graphData G)))
    (colorSize v) (colorSize v) k i j
  rw [hB] at hpad
  exact hpad.symm

theorem rawTensorEntry_cast {v : ℕ} (G : SimpleGraph (Fin v))
    (i j k : Fin (colorSize v)) :
    (rawTensorEntry v (graphData G) i.val j.val k.val : ℚ) = colorTensor G i j k := by
  rw [rawTensorEntry_graphData, intColorTensor_cast]

end TensorNP.Encoder
end


/- Inlined module: RawCountBounds -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.Encoder

theorem naturalMonomial_le (row col a b : ℕ) : naturalMonomial row col a b ≤ 1 := by
  unfold naturalMonomial
  split <;> omega

theorem neighborCount_le (v : ℕ) (data : List BSym) (vertex a b count : ℕ) :
    neighborCount v data vertex a b count ≤ 3 * count := by
  induction count with
  | zero => simp [neighborCount]
  | succ count ih =>
      have h1 := naturalMonomial_le vertex vertex a b
      have h2 := naturalMonomial_le vertex count a b
      have h3 := naturalMonomial_le count count a b
      simp only [neighborCount]
      split <;> omega

theorem rawPositiveCount_le (v : ℕ) (data : List BSym) (family vertex a b : ℕ) :
    rawPositiveCount v data family vertex a b ≤ 3*v+1 := by
  have h0 := naturalMonomial_le vertex (v+vertex) a b
  have h1 := naturalMonomial_le (v+vertex) (2*v) a b
  have h2 := naturalMonomial_le vertex (2*v) a b
  have h3 := neighborCount_le v data vertex a b v
  unfold rawPositiveCount
  split_ifs <;> omega

theorem rawNegativeCount_le (v family vertex a b : ℕ) :
    rawNegativeCount v family vertex a b ≤ 1 := by
  have h0 := naturalMonomial_le (2*v) (2*v) a b
  have h1 := naturalMonomial_le vertex vertex a b
  have h2 := naturalMonomial_le (v+vertex) (v+vertex) a b
  unfold rawNegativeCount
  split_ifs <;> omega

theorem rawCounts_le (v : ℕ) (data : List BSym) (family vertex a b : ℕ) :
    rawPositiveCount v data family vertex a b + rawNegativeCount v family vertex a b ≤ 3*v+2 := by
  have hp := rawPositiveCount_le v data family vertex a b
  have hn := rawNegativeCount_le v family vertex a b
  omega

end TensorNP.Encoder
end


/- Inlined module: EntryCounts -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Eigen
namespace TensorNP.Encoder

def countValue (p : ℕ × ℕ) : ℤ := (p.1 : ℤ)-(p.2 : ℤ)
def swapCounts (p : ℕ × ℕ) : ℕ × ℕ := (p.2,p.1)

def colorCounts (v : ℕ) (data : List BSym) (q a b : ℕ) : ℕ × ℕ :=
  (rawPositiveCount v data (q/v) (q%v) a b, rawNegativeCount v (q/v) (q%v) a b)

def splitCounts (m n : ℕ) (A : ℕ → ℕ → ℕ → ℕ × ℕ) (q a b : ℕ) : ℕ × ℕ :=
  if q < m then
    if a < n then (if b < n then A q a b else (0,0))
    else (if b < n then (0,0) else swapCounts (A q (a-n) (b-n)))
  else
    if a < n then (if b < n then (0,0) else A (q-m) a (b-n))
    else (if b < n then A (q-m) (a-n) b else (0,0))

def tensorCounts (v : ℕ) (data : List BSym) (i j k : ℕ) : ℕ × ℕ :=
  if k <8*v then
    if i <4*v+2 ∧ j <4*v+2 then splitCounts (4*v) (2*v+1) (colorCounts v data) k i j else (0,0)
  else if k+1=8*v+2 then (if 4*v+2 ≤ i ∧ i=j then (1,0) else (0,0)) else (0,0)

theorem splitCounts_value (m n : ℕ) (A : ℕ → ℕ → ℕ → ℕ × ℕ) (q a b : ℕ) :
    countValue (splitCounts m n A q a b) = rawRealSplit m n (fun q a b => countValue (A q a b)) q a b := by
  unfold splitCounts rawRealSplit
  split_ifs <;> simp [countValue, swapCounts]

theorem tensorCounts_value (v : ℕ) (data : List BSym) (i j k : ℕ) :
    countValue (tensorCounts v data i j k) = rawTensorEntry v data i j k := by
  have hA : (fun q a b => countValue (colorCounts v data q a b)) = rawColorMatrix v data := rfl
  unfold rawTensorEntry rawPadSystem
  have hm : 4*v+4*v=8*v := by omega
  have hn : 2*v+1+(2*v+1)=4*v+2 := by omega
  rw [hm, hn]
  unfold tensorCounts
  split_ifs
  · rw [splitCounts_value, hA]
  all_goals rfl

/-- Three bounded subtractions replace variable division in the executable evaluator. -/
def familyDecode (v q : ℕ) : ℕ × ℕ :=
  if q < v then (0,q) else if q-v < v then (1,q-v)
  else if q-v-v < v then (2,q-v-v) else (3,q-v-v-v)

theorem familyDecode_correct {v q : ℕ} (hq : q <4*v) : familyDecode v q = (q/v,q%v) := by
  unfold familyDecode
  split_ifs with h0 h1 h2
  · rw [Nat.div_eq_of_lt h0, Nat.mod_eq_of_lt h0]
  · have hd : q/v=1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hd, Nat.mod_eq_sub_mul_div]
  · have hd : q/v=2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hd, Nat.mod_eq_sub_mul_div, hd]
    congr 1
    omega
  · have hd : q/v=3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hd, Nat.mod_eq_sub_mul_div, hd]
    congr 1
    omega

theorem familyDecode_vertex_lt {v q : ℕ} (hq : q <4*v) : (familyDecode v q).2 < v := by
  rw [familyDecode_correct hq]
  exact Nat.mod_lt _ (by omega)

end TensorNP.Encoder
end


/- Inlined module: NativeWriter12 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def nativeWriterPorts12 : Fin 5 ↪ Fin 12 :=
  ⟨fun k => ⟨k.val, by omega⟩, by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 12 => x.val) h)⟩

def nativeWriterDecode12 (l : Fin 12) : Option (Fin 5) :=
  if h : l.val < 5 then some ⟨l.val, h⟩ else none

lemma nativeWriterDecode12_spec (l : Fin 12) (k : Fin 5) :
    nativeWriterDecode12 l = some k ↔ nativeWriterPorts12 k = l := by
  fin_cases l <;> fin_cases k <;> decide

def writerStore12 (n : ℕ) (tail : List BSym) (frame : Fin 7 → List BSym) : Fin 12 → List BSym :=
  fun k => if k = 0 then List.replicate n .one else if k = 1 then tail
    else if h : 5 ≤ k.val then frame ⟨k.val - 5, by omega⟩ else []

lemma writerStore12_project (n : ℕ) (tail : List BSym) (frame : Fin 7 → List BSym) :
    StackProgPortLift.project nativeWriterPorts12 (writerStore12 n tail frame) =
      fun k => if k = 0 then List.replicate n .one else if k = 1 then tail else [] := by
  funext k
  fin_cases k <;> rfl

private lemma native_write_at (t : Fin 5 → List BSym) (s : Fin 12 → List BSym) (k : Fin 5) :
    StackProgPortLift.write nativeWriterPorts12 t s (nativeWriterPorts12 k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := nativeWriterPorts12.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma writerStore12_write (n : ℕ) (tail result : List BSym) (frame : Fin 7 → List BSym) :
    StackProgPortLift.write nativeWriterPorts12
      (fun k => if k = 0 then List.replicate n .one else if k = 1 then result else [])
      (writerStore12 n tail frame) = writerStore12 n result frame := by
  classical
  funext l
  by_cases hl : l.val < 5
  · let k : Fin 5 := ⟨l.val, hl⟩
    have hk : nativeWriterPorts12 k = l := Fin.ext rfl
    rw [← hk, native_write_at]
    exact (congrFun (writerStore12_project n result frame) k).symm
  · have hout : ¬ ∃ k, nativeWriterPorts12 k = l := by
      rintro ⟨k, hk⟩
      have hv := congrArg Fin.val hk
      have hklt := k.isLt
      change k.val = l.val at hv
      omega
    have h0 : l ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      omega
    have h1 : l ≠ 1 := by
      intro he
      have hv := congrArg Fin.val he
      omega
    simp [StackProgPortLift.write, hout, writerStore12, h0, h1]

theorem nativeWriter12 :
    ∃ (p : StackProg (Fin 12) BSym) (C : ℕ),
      ∀ (n : ℕ) (tail : List BSym) (frame : Fin 7 → List BSym), ∃ steps,
        p.Exec (writerStore12 n tail frame) (writerStore12 n (encNat n ++ tail) frame) steps ∧
        steps ≤ C * (n + 1)^2 := by
  obtain ⟨p, C, hp⟩ := CookPvsNP.unary_to_encNat_stack
  refine ⟨StackProgPortLift.liftProgC nativeWriterPorts12 nativeWriterDecode12 p, C, ?_⟩
  intro n tail frame
  obtain ⟨steps, hs, hb⟩ := hp n tail
  refine ⟨steps, ?_, hb⟩
  have hlift := StackProgPortLift.liftProgC_exec nativeWriterPorts12 nativeWriterDecode12
    nativeWriterDecode12_spec hs (writerStore12 n tail frame)
    (writerStore12_project n tail frame)
  rw [writerStore12_write] at hlift
  exact hlift

end TensorNP.Encoder
end


/- Inlined module: Prefix12 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def prefixPorts12 : Fin 3 ↪ Fin 12 := ⟨![1, 6, 8], by decide⟩

def prefixDecode12 (l : Fin 12) : Option (Fin 3) :=
  if l = 1 then some 0 else if l = 6 then some 1 else if l = 8 then some 2 else none

lemma prefixDecode12_spec (l : Fin 12) (k : Fin 3) :
    prefixDecode12 l = some k ↔ prefixPorts12 k = l := by
  fin_cases l <;> fin_cases k <;> decide

def prefixFrameStore (pattern input status : List BSym) (frame : Fin 12 → List BSym) : Fin 12 → List BSym :=
  fun k => if k = 1 then pattern else if k = 6 then input else if k = 8 then status else frame k

def prefixProg12 : StackProg (Fin 12) BSym :=
  StackProgPortLift.liftProgC prefixPorts12 prefixDecode12 prefixProg

lemma prefixFrameStore_project (pattern input status : List BSym) (frame : Fin 12 → List BSym) :
    StackProgPortLift.project prefixPorts12 (prefixFrameStore pattern input status frame) =
      prefixStore pattern input status := by
  funext k
  fin_cases k <;> rfl

private lemma prefix_write_at (t : Fin 3 → List BSym) (s : Fin 12 → List BSym) (k : Fin 3) :
    StackProgPortLift.write prefixPorts12 t s (prefixPorts12 k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := prefixPorts12.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma prefixFrameStore_write (pattern input status pattern' input' status' : List BSym)
    (frame : Fin 12 → List BSym) :
    StackProgPortLift.write prefixPorts12 (prefixStore pattern' input' status')
      (prefixFrameStore pattern input status frame) = prefixFrameStore pattern' input' status' frame := by
  classical
  funext l
  by_cases hl : ∃ k, prefixPorts12 k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [prefix_write_at]
    exact (congrFun (prefixFrameStore_project pattern' input' status' frame) k).symm
  · have h1 : l ≠ 1 := by
      intro he
      apply hl
      exact ⟨0, he.symm⟩
    have h6 : l ≠ 6 := by
      intro he
      apply hl
      exact ⟨1, he.symm⟩
    have h8 : l ≠ 8 := by
      intro he
      apply hl
      exact ⟨2, he.symm⟩
    simp [StackProgPortLift.write, hl, prefixFrameStore, h1, h6, h8]

theorem prefixProg12_exec (pattern input status : List BSym) (frame : Fin 12 → List BSym) :
    prefixProg12.Exec (prefixFrameStore pattern input status frame)
      (prefixFrameStore (prefixResult pattern input).patternRest
        (prefixResult pattern input).inputRest
        ((if (prefixResult pattern input).patternRest = [] then BSym.one else .zero) :: status) frame)
      (3 * (prefixResult pattern input).matched + 3) := by
  have hlift := StackProgPortLift.liftProgC_exec prefixPorts12 prefixDecode12
    prefixDecode12_spec (prefixProg_exec pattern input status)
    (prefixFrameStore pattern input status frame)
    (prefixFrameStore_project pattern input status frame)
  rw [prefixFrameStore_write] at hlift
  exact hlift

end TensorNP.Encoder
end


/- Inlined module: HeaderBody -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

private lemma encNat_length_le (n : ℕ) : (encNat n).length ≤ n + 1 := by
  have hn : n.bits.length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self)
  simp only [encNat, List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

private lemma prefixResult_rest_lengths (pattern input : List BSym) :
    (prefixResult pattern input).patternRest.length ≤ pattern.length ∧
    (prefixResult pattern input).inputRest.length ≤ input.length := by
  induction pattern generalizing input with
  | nil => simp [prefixResult]
  | cons a pattern ih =>
      cases input with
      | nil => simp [prefixResult]
      | cons b input =>
          by_cases hab : a = b
          · simp only [prefixResult, if_pos hab, List.length_cons]
            have h := ih input
            omega
          · simp [prefixResult, hab]

private def bodyStore (n fuel : ℕ) (input pattern work status : List BSym) : Fin 12 → List BSym :=
  prefixFrameStore pattern work status (headerStore n fuel input [] false)

private def writerFrame (input : List BSym) (fuel : ℕ) : Fin 7 → List BSym :=
  fun k => if k = 0 then input else if k = 2 then List.replicate fuel .one else []

private lemma writerFrame_store (n fuel : ℕ) (input pattern : List BSym) :
    writerStore12 n pattern (writerFrame input fuel) = bodyStore n fuel input pattern [] [] := by
  funext k
  fin_cases k <;> rfl

private lemma bodyStore_initial (n fuel : ℕ) (input : List BSym) :
    bodyStore n fuel input [] [] [] = headerStore n fuel input [] false := by
  funext k
  fin_cases k <;> rfl

private lemma bodyStore_copied (n fuel : ℕ) (input pattern : List BSym) :
    Function.update (bodyStore n fuel input pattern [] []) 6
      ((bodyStore n fuel input pattern [] []) 5 ++ (bodyStore n fuel input pattern [] []) 6) =
      bodyStore n fuel input pattern input [] := by
  funext k
  fin_cases k <;> simp [Function.update, bodyStore, prefixFrameStore, headerStore]

private lemma clear_exec (k : Fin 12) (s : Fin 12 → List BSym) :
    (clearProg k).Exec s (Function.update s k []) (3 * (s k).length + 1) := by
  have hf : transferStore k (fun _ => false) s = Function.update s k [] := by
    funext j
    by_cases hj : j = k <;> simp [transferStore, Function.update, hj]
  simpa only [clearProg, hf] using stack_transfer k (fun _ => false) s

private def bodyTest (h : Fin 12 → Option BSym) : Bool := h 8 == some .one

private def bodyIncrement (_ : Fin 12 → Option BSym) (k : Fin 12) : StackAct BSym :=
  if k = 0 then .push .one else if k = 7 then .pop else .keep

private def bodyKeep : StackProg (Fin 12) BSym := .act (fun _ _ => .keep)

private def bodyFail : StackProg (Fin 12) BSym :=
  .seq (clearProg 1) (.seq (clearProg 6) (.seq (clearProg 8) (.act bodyIncrement)))

private def bodyProgram (writer : StackProg (Fin 12) BSym) : StackProg (Fin 12) BSym :=
  .seq writer (.seq (copyProg 5 6 9) (.seq prefixProg12 (.branch bodyTest bodyKeep bodyFail)))

private lemma bodyStore_found (n fuel : ℕ) (input work : List BSym) :
    bodyStore n fuel input [] work [.one] = headerStore n fuel input work true := by
  funext k
  fin_cases k <;> rfl

private lemma bodyStore_failure (n fuel : ℕ) (input pattern work : List BSym) (hf : 0 < fuel) :
    StackProg.applyAct bodyIncrement
      (Function.update (Function.update (Function.update
        (bodyStore n fuel input pattern work [.zero]) 1 []) 6 []) 8 []) =
      headerStore (n + 1) (fuel - 1) input [] false := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      funext k
      fin_cases k <;> simp [StackProg.applyAct, bodyIncrement, StackAct.apply,
        Function.update, bodyStore, prefixFrameStore, headerStore, List.replicate_succ]

private lemma bodyFail_exec (n fuel : ℕ) (input pattern work : List BSym) (hf : 0 < fuel) :
    bodyFail.Exec (bodyStore n fuel input pattern work [.zero])
      (headerStore (n + 1) (fuel - 1) input [] false)
      (3 * pattern.length + 3 * work.length + 10) := by
  let s0 := bodyStore n fuel input pattern work [.zero]
  let s1 := Function.update s0 1 []
  let s2 := Function.update s1 6 []
  let s3 := Function.update s2 8 []
  have he1 : (clearProg 1).Exec s0 s1 (3 * pattern.length + 1) := by
    simpa [s0, s1, bodyStore, prefixFrameStore] using clear_exec 1 s0
  have he2 : (clearProg 6).Exec s1 s2 (3 * work.length + 1) := by
    simpa [s0, s1, s2, bodyStore, prefixFrameStore] using clear_exec 6 s1
  have he3 : (clearProg 8).Exec s2 s3 4 := by
    simpa [s0, s1, s2, s3, bodyStore, prefixFrameStore] using clear_exec 8 s2
  have he4 : (StackProg.act bodyIncrement).Exec s3
      (headerStore (n + 1) (fuel - 1) input [] false) 1 := by
    have he := StackProg.Exec.act bodyIncrement s3
    have heq : StackProg.applyAct bodyIncrement s3 =
        headerStore (n + 1) (fuel - 1) input [] false := by
      simpa only [s0, s1, s2, s3] using bodyStore_failure n fuel input pattern work hf
    rw [heq] at he
    exact he
  have he := StackProg.Exec.seq he1 (StackProg.Exec.seq he2 (StackProg.Exec.seq he3 he4))
  convert he using 1 <;> first | rfl | omega

private lemma bodyBranch_exec (n fuel : ℕ) (input : List BSym) (hf : 0 < fuel) :
    ∃ steps, (StackProg.branch bodyTest bodyKeep bodyFail).Exec
      (bodyStore n fuel input (prefixResult (encNat n) input).patternRest
        (prefixResult (encNat n) input).inputRest
        [if (prefixResult (encNat n) input).patternRest = [] then .one else .zero])
      (headerStepResult n fuel input) steps ∧
      steps ≤ 3 * (prefixResult (encNat n) input).patternRest.length +
        3 * (prefixResult (encNat n) input).inputRest.length + 11 := by
  by_cases hm : (prefixResult (encNat n) input).patternRest = []
  · let s := bodyStore n fuel input [] (prefixResult (encNat n) input).inputRest [.one]
    have ht : bodyTest (fun k => (s k).head?) = true := by
      simp [s, bodyTest, bodyStore, prefixFrameStore]
    have he : bodyKeep.Exec s s 1 := by
      have hid : StackProg.applyAct (fun _ _ => StackAct.keep) s = s := by
        funext k
        rfl
      simpa only [bodyKeep, hid] using
        (StackProg.Exec.act (fun _ _ => StackAct.keep) s)
    refine ⟨2, ?_, by omega⟩
    simpa [s, hm, headerStepResult, bodyStore_found] using
      (StackProg.Exec.branchTrue (q := bodyFail) ht he)
  · let s := bodyStore n fuel input (prefixResult (encNat n) input).patternRest
        (prefixResult (encNat n) input).inputRest [.zero]
    have ht : bodyTest (fun k => (s k).head?) = false := by
      simp [s, bodyTest, bodyStore, prefixFrameStore]
    have he := bodyFail_exec n fuel input (prefixResult (encNat n) input).patternRest
      (prefixResult (encNat n) input).inputRest hf
    refine ⟨1 + (3 * (prefixResult (encNat n) input).patternRest.length +
      3 * (prefixResult (encNat n) input).inputRest.length + 10), ?_, by omega⟩
    simpa [s, hm, headerStepResult] using
      (StackProg.Exec.branchFalse (p := bodyKeep) ht he)

theorem header_body_exists :
    ∃ (body : StackProg (Fin 12) BSym) (C : ℕ),
      ∀ (input : List BSym) (n fuel : ℕ), 0 < fuel → n + fuel ≤ input.length + 1 →
        ∃ steps, body.Exec (headerStore n fuel input [] false)
          (headerStepResult n fuel input) steps ∧ steps ≤ C * (input.length + 2)^2 := by
  obtain ⟨writer, C, hw⟩ := nativeWriter12
  refine ⟨bodyProgram writer, C + 100, ?_⟩
  intro input n fuel hf hbudget
  obtain ⟨wt, heW, hwt⟩ := hw n [] (writerFrame input fuel)
  have heW' : writer.Exec (headerStore n fuel input [] false)
      (bodyStore n fuel input (encNat n) [] []) wt := by
    simpa only [writerFrame_store, bodyStore_initial, List.append_nil] using heW
  have heC : (copyProg 5 6 9).Exec (bodyStore n fuel input (encNat n) [] [])
      (bodyStore n fuel input (encNat n) input []) (6 * input.length + 3) := by
    have hc := stack_copy (5 : Fin 12) 6 9 (by decide) (by decide) (by decide)
      (bodyStore n fuel input (encNat n) [] []) (by rfl)
    rw [bodyStore_copied] at hc
    simpa [bodyStore, prefixFrameStore, headerStore] using hc
  have heP : prefixProg12.Exec (bodyStore n fuel input (encNat n) input [])
      (bodyStore n fuel input (prefixResult (encNat n) input).patternRest
        (prefixResult (encNat n) input).inputRest
        [if (prefixResult (encNat n) input).patternRest = [] then .one else .zero])
      (3 * (prefixResult (encNat n) input).matched + 3) :=
    prefixProg12_exec (encNat n) input [] (headerStore n fuel input [] false)
  obtain ⟨bt, heB, hbt⟩ := bodyBranch_exec n fuel input hf
  have he := StackProg.Exec.seq heW' (StackProg.Exec.seq heC (StackProg.Exec.seq heP heB))
  refine ⟨_, he, ?_⟩
  have hn : n ≤ input.length := by omega
  have hp : (prefixResult (encNat n) input).patternRest.length ≤ input.length + 1 := by
    have h := (prefixResult_rest_lengths (encNat n) input).1
    have henc := encNat_length_le n
    omega
  have hi := (prefixResult_rest_lengths (encNat n) input).2
  have hm := prefixResult_matched_le_input (encNat n) input
  have hL : input.length + 2 ≤ (input.length + 2)^2 := by nlinarith
  have hwt' : wt ≤ C * (input.length + 2)^2 :=
    hwt.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) 2))
  have hsum : wt + 1 + (6 * input.length + 3 + 1 +
      (3 * (prefixResult (encNat n) input).matched + 3 + 1 + bt)) ≤
      C * (input.length + 2)^2 + 100 * (input.length + 2)^2 := by omega
  calc
    _ ≤ C * (input.length + 2)^2 + 100 * (input.length + 2)^2 := hsum
    _ = _ := by ring

end TensorNP.Encoder
end


/- Inlined module: HeaderInit -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def headerInputStore (input : List BSym) : Fin 12 → List BSym :=
  fun k => if k = 5 then input else []

private def initStore (input scratch fuel : List BSym) : Fin 12 → List BSym :=
  fun k => if k = 5 then input else if k = 9 then scratch else if k = 7 then fuel else []

private def initGuard (h : Fin 12 → Option BSym) : Bool := (h 5).isSome

private def initAct (h : Fin 12 → Option BSym) (k : Fin 12) : StackAct BSym :=
  if k = 5 then .pop else if k = 9 then
    match h 5 with | some a => .push a | none => .keep
  else if k = 7 then .push .one else .keep

private def initLoop : StackProg (Fin 12) BSym := .loop initGuard (.act initAct)

private def initRestore : StackProg (Fin 12) BSym :=
  transferProg 9 (fun k => decide (k = 5))

private def initProgram : StackProg (Fin 12) BSym :=
  .seq initLoop (.seq initRestore (pushProg 7 .one))

private lemma initAct_step (a : BSym) (input scratch fuel : List BSym) :
    StackProg.applyAct initAct (initStore (a :: input) scratch fuel) =
      initStore input (a :: scratch) (.one :: fuel) := by
  funext k
  fin_cases k <;> rfl

private lemma initLoop_exec (input scratch fuel : List BSym) :
    initLoop.Exec (initStore input scratch fuel)
      (initStore [] (input.reverse ++ scratch) (List.replicate input.length BSym.one ++ fuel))
      (3 * input.length + 1) := by
  induction input generalizing scratch fuel with
  | nil =>
      exact StackProg.Exec.loopFalse (by rfl)
  | cons a input ih =>
      have hg : initGuard (fun k => (initStore (a :: input) scratch fuel k).head?) = true := by rfl
      have ha : (StackProg.act initAct).Exec (initStore (a :: input) scratch fuel)
          (initStore input (a :: scratch) (.one :: fuel)) 1 := by
        simpa only [initAct_step] using (StackProg.Exec.act initAct
          (initStore (a :: input) scratch fuel))
      have he := StackProg.Exec.loopTrue hg ha (ih (a :: scratch) (.one :: fuel))
      have hrep (m : ℕ) : List.replicate m BSym.one ++ .one :: fuel =
          .one :: (List.replicate m BSym.one ++ fuel) := by
        induction m with
        | zero => rfl
        | succ m ih => simp [List.replicate_succ, ih]
      simpa [initLoop, List.reverse_cons, List.append_assoc, List.replicate_succ, hrep,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

theorem header_init_exists : ∃ p : StackProg (Fin 12) BSym, ∀ input : List BSym,
    p.Exec (headerInputStore input)
      (headerStore 0 (input.length + 1) input [] false) (6 * input.length + 5) := by
  refine ⟨initProgram, ?_⟩
  intro input
  have hstart : initStore input [] [] = headerInputStore input := by
    funext k
    fin_cases k <;> rfl
  have heLoop : initLoop.Exec (headerInputStore input)
      (initStore [] input.reverse (List.replicate input.length .one)) (3 * input.length + 1) := by
    simpa only [hstart, List.append_nil] using initLoop_exec input [] []
  have hrestore : transferStore (9 : Fin 12) (fun k => decide (k = 5))
      (initStore [] input.reverse (List.replicate input.length .one)) =
      initStore input [] (List.replicate input.length .one) := by
    funext k
    fin_cases k <;> simp [transferStore, initStore]
  have heRestore : initRestore.Exec (initStore [] input.reverse (List.replicate input.length .one))
      (initStore input [] (List.replicate input.length .one)) (3 * input.length + 1) := by
    have he := stack_transfer (9 : Fin 12) (fun k => decide (k = 5))
      (initStore [] input.reverse (List.replicate input.length .one))
    rw [hrestore] at he
    simpa [initRestore, initStore] using he
  have hePush : (pushProg 7 .one).Exec (initStore input [] (List.replicate input.length .one))
      (headerStore 0 (input.length + 1) input [] false) 1 := by
    have heq : StackProg.applyAct (fun _ k => if k = 7 then .push BSym.one else .keep)
        (initStore input [] (List.replicate input.length .one)) =
        headerStore 0 (input.length + 1) input [] false := by
      funext k
      fin_cases k <;> simp [StackProg.applyAct, StackAct.apply, initStore, headerStore,
        List.replicate_succ]
    simpa only [pushProg, heq] using (StackProg.Exec.act
      (fun _ k => if k = 7 then .push BSym.one else .keep)
      (initStore input [] (List.replicate input.length .one)))
  convert StackProg.Exec.seq heLoop (StackProg.Exec.seq heRestore hePush) using 1 <;>
    first | rfl | omega

end TensorNP.Encoder
end


/- Inlined module: HeaderMachine -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

theorem nativeHeaderSearch :
    ∃ (p : StackProg (Fin 12) BSym) (C : ℕ), ∀ input : List BSym, ∃ steps,
      p.Exec (headerStore 0 (input.length+1) input [] false)
        (headerResultStore (boundedHeader 0 (input.length+1) input) input) steps ∧
      steps ≤ C * (input.length+2)^3 := by
  obtain ⟨body, C, hbody⟩ := header_body_exists
  refine ⟨.loop headerGuard body, C+3, fun input => ?_⟩
  obtain ⟨steps, hs, hb⟩ := headerLoop_exec body (C*(input.length+2)^2) input
    (fun n fuel hf hbudget => hbody input n fuel hf hbudget)
    (input.length+1) 0 (by omega)
  refine ⟨steps, hs, hb.trans ?_⟩
  have hmul := Nat.mul_le_mul_right (C*(input.length+2)^2+2)
    (show input.length+1 ≤ input.length+2 by omega)
  have hcube : input.length+2 ≤ (input.length+2)^3 :=
    Nat.le_self_pow (by decide) _
  calc
    (input.length+1)*(C*(input.length+2)^2+2)+1 ≤
        (input.length+2)*(C*(input.length+2)^2+2)+1 := by omega
    _ = C*(input.length+2)^3 + 2*(input.length+2)+1 := by ring
    _ ≤ (C+3)*(input.length+2)^3 := by nlinarith

theorem header_parser_source :
    ∃ (p : StackProg (Fin 12) BSym) (C : ℕ), ∀ input : List BSym, ∃ steps,
      p.Exec (headerInputStore input)
        (headerResultStore (boundedHeader 0 (input.length+1) input) input) steps ∧
      steps ≤ C * (input.length+2)^3 := by
  obtain ⟨init, hi⟩ := header_init_exists
  obtain ⟨search, C, hs⟩ := nativeHeaderSearch
  refine ⟨.seq init search, C+8, fun input => ?_⟩
  obtain ⟨steps, hsteps, hbound⟩ := hs input
  refine ⟨(6*input.length+5)+1+steps, StackProg.Exec.seq (hi input) hsteps, ?_⟩
  have hcube : input.length+2 ≤ (input.length+2)^3 := Nat.le_self_pow (by decide) _
  calc
    (6*input.length+5)+1+steps ≤
        C*(input.length+2)^3 + 8*(input.length+2)^3 := by omega
    _ = _ := by ring

end TensorNP.Encoder
end


/- Inlined module: MatrixLookup12 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def checkerWorkStore (n row col : ℕ) (data output read : List BSym) (good : Bool) : Fin 12 → List BSym :=
  fun k => if k = 4 then output else if k = 11 then read else checkerStore n row col data good k

def lookupPorts12 : Bool → (Fin 8 ↪ Fin 12)
  | false => ⟨![0, 1, 2, 3, 4, 5, 6, 7], by decide⟩
  | true => ⟨![0, 1, 3, 2, 4, 5, 6, 7], by decide⟩

def lookupDecode12 (swapped : Bool) (l : Fin 12) : Option (Fin 8) :=
  if l = 0 then some 0 else if l = 1 then some 1
  else if l = 2 then some (if swapped then 3 else 2)
  else if l = 3 then some (if swapped then 2 else 3)
  else if l = 4 then some 4 else if l = 5 then some 5 else if l = 6 then some 6
  else if l = 7 then some 7 else none

lemma lookupDecode12_spec (swapped : Bool) (l : Fin 12) (k : Fin 8) :
    lookupDecode12 swapped l = some k ↔ lookupPorts12 swapped k = l := by
  cases swapped <;> fin_cases l <;> fin_cases k <;> decide

def lookupProg12 (swapped : Bool) : StackProg (Fin 12) BSym :=
  StackProgPortLift.liftProgC (lookupPorts12 swapped) (lookupDecode12 swapped)
    TensorAdjacencyLookup8.lookupProg

def checkerLookupStore (swapped : Bool) (n i j : ℕ) (data output : List BSym) : Fin 8 → List BSym :=
  TensorAdjacencyLookup8.store data (List.replicate n .one)
    (List.replicate (if swapped then j else i) .one)
    (List.replicate (if swapped then i else j) .one) output [] [] []

lemma checkerWorkStore_project (swapped : Bool) (n i j : ℕ) (data output read : List BSym)
    (good : Bool) : StackProgPortLift.project (lookupPorts12 swapped)
      (checkerWorkStore n i j data output read good) = checkerLookupStore swapped n i j data output := by
  funext k
  cases swapped <;> fin_cases k <;> rfl

private lemma lookup_write_at (swapped : Bool) (t : Fin 8 → List BSym)
    (s : Fin 12 → List BSym) (k : Fin 8) :
    StackProgPortLift.write (lookupPorts12 swapped) t s (lookupPorts12 swapped k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := (lookupPorts12 swapped).injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma checkerWorkStore_write (swapped : Bool) (n i j : ℕ) (data output output' read : List BSym)
    (good : Bool) : StackProgPortLift.write (lookupPorts12 swapped)
      (checkerLookupStore swapped n i j data output') (checkerWorkStore n i j data output read good) =
      checkerWorkStore n i j data output' read good := by
  classical
  funext l
  by_cases hl : ∃ k, lookupPorts12 swapped k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [lookup_write_at]
    exact (congrFun (checkerWorkStore_project swapped n i j data output' read good) k).symm
  · have hx : l.val < 8 → ∃ k, lookupPorts12 swapped k = l := by
      cases swapped <;> fin_cases l <;> decide
    have h4 : l ≠ 4 := by
      intro h
      subst l
      exact hl (hx (by decide))
    simp [StackProgPortLift.write, hl, checkerWorkStore, h4]

lemma checkerWorkStore_empty (n i j : ℕ) (data : List BSym) (good : Bool) :
    checkerWorkStore n i j data [] [] good = checkerStore n i j data good := by
  funext k
  fin_cases k <;> rfl

theorem lookupProg12_exec (swapped : Bool) (n i j : ℕ) (data output read : List BSym)
    (good : Bool) (hi : i < n) (hj : j < n) (hlen : data.length = n*n) :
    ∃ steps, steps ≤ 50*(n+1)^2 ∧
      (lookupProg12 swapped).Exec (checkerWorkStore n i j data output read good)
        (checkerWorkStore n i j data
          ((if swapped then data.getD (j*n+i) .zero else data.getD (i*n+j) .zero) :: output)
          read good) steps := by
  have hi' : (if swapped then j else i) < n := by cases swapped <;> simp_all
  have hj' : (if swapped then i else j) < n := by cases swapped <;> simp_all
  obtain ⟨steps, hbound, he⟩ := TensorAdjacencyLookup8.lookupProg_exec n
    (if swapped then j else i) (if swapped then i else j) data output hi' hj' hlen
  have hx : TensorAdjacencyLookup8.lookupProg.Exec
      (checkerLookupStore swapped n i j data output)
      (checkerLookupStore swapped n i j data
        (data.getD ((if swapped then j else i)*n+(if swapped then i else j)) .zero :: output)) steps := by
    exact he
  have hlift := StackProgPortLift.liftProgC_exec (lookupPorts12 swapped) (lookupDecode12 swapped)
    (lookupDecode12_spec swapped) hx (checkerWorkStore n i j data output read good)
    (checkerWorkStore_project swapped n i j data output read good)
  rw [checkerWorkStore_write] at hlift
  refine ⟨steps, hbound, ?_⟩
  cases swapped <;> simpa [lookupProg12] using hlift

end TensorNP.Encoder
end


/- Inlined module: MatrixCheckLoops -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def checkerColGuard (h : Fin 12 → Option BSym) : Bool := (h 3).isSome

def checkerRowGuard (h : Fin 12 → Option BSym) : Bool := (h 2).isSome

theorem symmetry_loop_exec (body : StackProg (Fin 12) BSym) (B n row : ℕ) (data : List BSym)
    (hstep : ∀ j : ℕ, j < n → ∀ good : Bool, ∃ steps,
      body.Exec (checkerStore n row (j+1) data good)
        (checkerStore n row j data
          (good && decide (data.getD (row*n+j) .zero = data.getD (j*n+row) .zero))) steps ∧ steps ≤ B) :
    ∀ count : ℕ, count ≤ n → ∀ good : Bool, ∃ steps,
      (StackProg.loop checkerColGuard body).Exec (checkerStore n row count data good)
        (checkerStore n row 0 data (good && symmetryPrefix n data row count)) steps ∧
      steps ≤ count*(B+2)+1 := by
  intro count
  induction count with
  | zero =>
      intro _ good
      refine ⟨1, ?_, by simp⟩
      simpa [symmetryPrefix] using
        (StackProg.Exec.loopFalse (p := body) (test := checkerColGuard)
          (s := checkerStore n row 0 data good) (by simp [checkerColGuard, checkerStore]))
  | succ count ih =>
      intro hc good
      obtain ⟨m, hm, hmB⟩ := hstep count (by omega) good
      obtain ⟨r, hr, hrB⟩ := ih (by omega)
        (good && decide (data.getD (row*n+count) .zero = data.getD (count*n+row) .zero))
      refine ⟨1+m+1+r, ?_, ?_⟩
      · simpa [symmetryPrefix, Bool.and_assoc] using
          (StackProg.Exec.loopTrue (test := checkerColGuard)
            (by simp [checkerColGuard, checkerStore, List.replicate_succ]) hm hr)
      · nlinarith

theorem matrix_loop_exec (body : StackProg (Fin 12) BSym) (B n : ℕ) (data : List BSym)
    (hstep : ∀ i : ℕ, i < n → ∀ good : Bool, ∃ steps,
      body.Exec (checkerStore n (i+1) 0 data good)
        (checkerStore n i 0 data
          (good && decide (data.getD (i*n+i) .zero = BSym.zero) && symmetryPrefix n data i n)) steps ∧
      steps ≤ B) :
    ∀ count : ℕ, count ≤ n → ∀ good : Bool, ∃ steps,
      (StackProg.loop checkerRowGuard body).Exec (checkerStore n count 0 data good)
        (checkerStore n 0 0 data (good && matrixCheckPrefix n data count)) steps ∧
      steps ≤ count*(B+2)+1 := by
  intro count
  induction count with
  | zero =>
      intro _ good
      refine ⟨1, ?_, by simp⟩
      simpa [matrixCheckPrefix] using
        (StackProg.Exec.loopFalse (p := body) (test := checkerRowGuard)
          (s := checkerStore n 0 0 data good) (by simp [checkerRowGuard, checkerStore]))
  | succ count ih =>
      intro hc good
      obtain ⟨m, hm, hmB⟩ := hstep count (by omega) good
      obtain ⟨r, hr, hrB⟩ := ih (by omega)
        (good && decide (data.getD (count*n+count) .zero = BSym.zero) && symmetryPrefix n data count n)
      refine ⟨1+m+1+r, ?_, ?_⟩
      · simpa [matrixCheckPrefix, Bool.and_assoc] using
          (StackProg.Exec.loopTrue (test := checkerRowGuard)
            (by simp [checkerRowGuard, checkerStore, List.replicate_succ]) hm hr)
      · nlinarith

end TensorNP.Encoder
end


/- Inlined module: MatrixCoordinates -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def symmetrySave (h : Fin 12 → Option BSym) (k : Fin 12) : StackAct BSym :=
  if k = 4 then .pop else if k = 11 then
    match h 4 with | some a => .push a | none => .keep
  else .keep

def symmetryMark (h : Fin 12 → Option BSym) (k : Fin 12) : StackAct BSym :=
  if k = 4 ∨ k = 11 then .pop
  else if k = 8 ∧ h 8 = none ∧ h 4 ≠ h 11 then .push .zero else .keep

def symmetryBody : StackProg (Fin 12) BSym :=
  .seq (popProg 3) (.seq (lookupProg12 false) (.seq (.act symmetrySave)
    (.seq (lookupProg12 true) (.act symmetryMark))))

theorem symmetrySave_step (n row col : ℕ) (data : List BSym) (a : BSym) (good : Bool) :
    StackProg.applyAct symmetrySave (checkerWorkStore n row col data [a] [] good) =
      checkerWorkStore n row col data [] [a] good := by
  funext k
  fin_cases k <;> rfl

theorem symmetryMark_step (n row col : ℕ) (data : List BSym) (a b : BSym) (good : Bool) :
    StackProg.applyAct symmetryMark (checkerWorkStore n row col data [b] [a] good) =
      checkerStore n row col data (good && decide (a = b)) := by
  cases good <;> cases a <;> cases b <;> funext k <;> fin_cases k <;> rfl

theorem checkerPopCol_exec (n row col : ℕ) (data : List BSym) (good : Bool) :
    (popProg (3 : Fin 12)).Exec (checkerStore n row (col+1) data good)
      (checkerStore n row col data good) 1 := by
  have heq : Function.update (checkerStore n row (col+1) data good) 3
      ((checkerStore n row (col+1) data good) 3).tail = checkerStore n row col data good := by
    funext k
    fin_cases k <;> simp [checkerStore, Function.update, List.replicate_succ]
  simpa only [heq] using (stack_basic_macros (3 : Fin 12)
    (checkerStore n row (col+1) data good)).2.1

theorem symmetryBody_exec (n row col : ℕ) (data : List BSym) (good : Bool)
    (hrow : row < n) (hcol : col < n) (hlen : data.length = n*n) :
    ∃ steps, symmetryBody.Exec (checkerStore n row (col+1) data good)
      (checkerStore n row col data
        (good && decide (data.getD (row*n+col) .zero = data.getD (col*n+row) .zero))) steps ∧
      steps ≤ 107*(n+1)^2 := by
  let a := data.getD (row*n+col) BSym.zero
  let b := data.getD (col*n+row) BSym.zero
  obtain ⟨u, huB, hu⟩ := lookupProg12_exec false n row col data [] [] good hrow hcol hlen
  rw [checkerWorkStore_empty] at hu
  obtain ⟨v, hvB, hv⟩ := lookupProg12_exec true n row col data [] [a] good hrow hcol hlen
  have hsave : (StackProg.act symmetrySave).Exec
      (checkerWorkStore n row col data [a] [] good)
      (checkerWorkStore n row col data [] [a] good) 1 := by
    simpa only [symmetrySave_step] using StackProg.Exec.act symmetrySave
      (checkerWorkStore n row col data [a] [] good)
  have hmark : (StackProg.act symmetryMark).Exec
      (checkerWorkStore n row col data [b] [a] good)
      (checkerStore n row col data (good && decide (a=b))) 1 := by
    simpa only [symmetryMark_step] using StackProg.Exec.act symmetryMark
      (checkerWorkStore n row col data [b] [a] good)
  have hex := StackProg.Exec.seq (checkerPopCol_exec n row col data good)
    (StackProg.Exec.seq hu (StackProg.Exec.seq hsave (StackProg.Exec.seq hv hmark)))
  refine ⟨_, hex, ?_⟩
  have hsq : 1 ≤ (n+1)^2 := Nat.one_le_pow 2 (n+1) (by omega)
  omega

def symmetryProgram : StackProg (Fin 12) BSym := .loop checkerColGuard symmetryBody

theorem symmetryProgram_exec (n row count : ℕ) (data : List BSym) (good : Bool)
    (hrow : row < n) (hcount : count ≤ n) (hlen : data.length = n*n) :
    ∃ steps, symmetryProgram.Exec (checkerStore n row count data good)
      (checkerStore n row 0 data (good && symmetryPrefix n data row count)) steps ∧
      steps ≤ 110*(n+1)^3 := by
  obtain ⟨steps, hs, hb⟩ := symmetry_loop_exec symmetryBody (107*(n+1)^2) n row data
    (fun j hj good => symmetryBody_exec n row j data good hrow hj hlen) count hcount good
  refine ⟨steps, hs, hb.trans ?_⟩
  have hm := Nat.mul_le_mul_right (107*(n+1)^2+2) (show count ≤ n+1 by omega)
  have hcube : n+1 ≤ (n+1)^3 := Nat.le_self_pow (by decide) _
  calc
    count*(107*(n+1)^2+2)+1 ≤ (n+1)*(107*(n+1)^2+2)+1 := by omega
    _ = 107*(n+1)^3+2*(n+1)+1 := by ring
    _ ≤ 110*(n+1)^3 := by omega

end TensorNP.Encoder
end


/- Inlined module: MatrixRow -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def diagonalMark (h : Fin 12 → Option BSym) (k : Fin 12) : StackAct BSym :=
  if k = 4 then .pop else if k = 8 ∧ h 8 = none ∧ h 4 ≠ some .zero then .push .zero else .keep

def matrixRowBody : StackProg (Fin 12) BSym :=
  .seq (popProg 2) (.seq (copyProg 2 3 7) (.seq (lookupProg12 false)
    (.seq (.act diagonalMark) (.seq (clearProg 3) (.seq (copyProg 1 3 7) symmetryProgram)))))

lemma diagonalMark_step (n row col : ℕ) (data : List BSym) (a : BSym) (good : Bool) :
    StackProg.applyAct diagonalMark (checkerWorkStore n row col data [a] [] good) =
      checkerStore n row col data (good && decide (a = .zero)) := by
  cases good <;> cases a <;> funext k <;> fin_cases k <;> rfl

lemma checkerPopRow_exec (n row : ℕ) (data : List BSym) (good : Bool) :
    (popProg (2 : Fin 12)).Exec (checkerStore n (row+1) 0 data good)
      (checkerStore n row 0 data good) 1 := by
  have hu : Function.update (checkerStore n (row+1) 0 data good) 2
      ((checkerStore n (row+1) 0 data good) 2).tail = checkerStore n row 0 data good := by
    funext k
    fin_cases k <;> simp [checkerStore, Function.update, List.replicate_succ]
  simpa only [hu] using (stack_basic_macros (2 : Fin 12)
    (checkerStore n (row+1) 0 data good)).2.1

lemma checkerCopyRow_exec (n row : ℕ) (data : List BSym) (good : Bool) :
    (copyProg (2 : Fin 12) 3 7).Exec (checkerStore n row 0 data good)
      (checkerStore n row row data good) (6*row+3) := by
  have h := stack_copy (2 : Fin 12) 3 7 (by decide) (by decide) (by decide)
    (checkerStore n row 0 data good) (by simp [checkerStore])
  have hu : Function.update (checkerStore n row 0 data good) 3
      (checkerStore n row 0 data good 2 ++ checkerStore n row 0 data good 3) =
        checkerStore n row row data good := by
    funext k
    fin_cases k <;> simp [checkerStore]
  rw [hu] at h
  simpa [checkerStore] using h

lemma checkerClearCol_exec (n row : ℕ) (data : List BSym) (good : Bool) :
    (clearProg (3 : Fin 12)).Exec (checkerStore n row row data good)
      (checkerStore n row 0 data good) (3*row+1) := by
  have hu : Function.update (checkerStore n row row data good) 3 [] =
      checkerStore n row 0 data good := by
    funext k
    fin_cases k <;> simp [checkerStore]
  have he := (stack_basic_macros (3 : Fin 12) (checkerStore n row row data good)).2.2
  rw [hu] at he
  simpa [checkerStore] using he

lemma checkerCopyDimension_exec (n row : ℕ) (data : List BSym) (good : Bool) :
    (copyProg (1 : Fin 12) 3 7).Exec (checkerStore n row 0 data good)
      (checkerStore n row n data good) (6*n+3) := by
  have h := stack_copy (1 : Fin 12) 3 7 (by decide) (by decide) (by decide)
    (checkerStore n row 0 data good) (by simp [checkerStore])
  have hu : Function.update (checkerStore n row 0 data good) 3
      (checkerStore n row 0 data good 1 ++ checkerStore n row 0 data good 3) =
        checkerStore n row n data good := by
    funext k
    fin_cases k <;> simp [checkerStore]
  rw [hu] at h
  simpa [checkerStore] using h

theorem matrix_row_body_exists : ∃ body : StackProg (Fin 12) BSym,
    ∀ (n row : ℕ) (data : List BSym) (good : Bool), row < n → data.length = n*n → ∃ steps,
      body.Exec (checkerStore n (row+1) 0 data good)
        (checkerStore n row 0 data
          (good && decide (data.getD (row*n+row) .zero = BSym.zero) && symmetryPrefix n data row n)) steps ∧
      steps ≤ 500*(n+1)^3 := by
  refine ⟨matrixRowBody, ?_⟩
  intro n row data good hrow hlen
  let a := data.getD (row*n+row) BSym.zero
  let good' := good && decide (a = BSym.zero)
  obtain ⟨u, huB, hu⟩ := lookupProg12_exec false n row row data [] [] good hrow hrow hlen
  rw [checkerWorkStore_empty] at hu
  have hmark : (StackProg.act diagonalMark).Exec
      (checkerWorkStore n row row data [a] [] good) (checkerStore n row row data good') 1 := by
    simpa only [diagonalMark_step] using StackProg.Exec.act diagonalMark
      (checkerWorkStore n row row data [a] [] good)
  obtain ⟨v, hv, hvB⟩ := symmetryProgram_exec n row n data good' hrow (by rfl) hlen
  have he := StackProg.Exec.seq (checkerPopRow_exec n row data good)
    (StackProg.Exec.seq (checkerCopyRow_exec n row data good)
      (StackProg.Exec.seq hu (StackProg.Exec.seq hmark
        (StackProg.Exec.seq (checkerClearCol_exec n row data good')
          (StackProg.Exec.seq (checkerCopyDimension_exec n row data good') hv)))))
  refine ⟨_, he, ?_⟩
  have hs : (n+1)^2 ≤ (n+1)^3 := pow_le_pow_right₀ (by omega) (by omega)
  have hn : n+1 ≤ (n+1)^3 := Nat.le_self_pow (by decide) _
  omega

end TensorNP.Encoder
end


/- Inlined module: MatrixMachine -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

theorem checkerCopyRowCounter (n : ℕ) (data : List BSym) (good : Bool) :
    (copyProg (1 : Fin 12) 2 7).Exec (checkerStore n 0 0 data good)
      (checkerStore n n 0 data good) (6*n+3) := by
  have hc := stack_copy (1 : Fin 12) 2 7 (by decide) (by decide) (by decide)
    (checkerStore n 0 0 data good) (by simp [checkerStore])
  have heq : Function.update (checkerStore n 0 0 data good) 2
      (checkerStore n 0 0 data good 1 ++ checkerStore n 0 0 data good 2) =
      checkerStore n n 0 data good := by
    funext k
    fin_cases k <;> simp [checkerStore]
  rw [heq] at hc
  simpa [checkerStore] using hc

theorem matrix_checker_source : ∃ p : StackProg (Fin 12) BSym,
    ∀ (n : ℕ) (data : List BSym) (good : Bool), data.length = n*n → ∃ steps,
      p.Exec (checkerStore n 0 0 data good)
        (checkerStore n 0 0 data (good && matrixCheckPrefix n data n)) steps ∧
      steps ≤ 1000*(n+1)^4 := by
  obtain ⟨body, hbody⟩ := matrix_row_body_exists
  refine ⟨.seq (copyProg 1 2 7) (.loop checkerRowGuard body), ?_⟩
  intro n data good hlen
  obtain ⟨steps, hs, hb⟩ := matrix_loop_exec body (500*(n+1)^3) n data
    (fun i hi good => hbody n i data good hi hlen) n le_rfl good
  refine ⟨(6*n+3)+1+steps, StackProg.Exec.seq (checkerCopyRowCounter n data good) hs, ?_⟩
  have hm := Nat.mul_le_mul_right (500*(n+1)^3+2) (show n ≤ n+1 by omega)
  have hquart : n+1 ≤ (n+1)^4 := Nat.le_self_pow (by decide) _
  calc
    (6*n+3)+1+steps ≤ (6*n+4)+((n+1)*(500*(n+1)^3+2)+1) := by omega
    _ = 500*(n+1)^4+8*n+7 := by ring
    _ ≤ 1000*(n+1)^4 := by omega

end TensorNP.Encoder
end


/- Inlined module: FrontendSpec -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

/-- Global frontend layout: original0, dimension1, suffix2, reversedbits3,
status4, reserved output5, unaryfuel6, row-major matrix7; remaining ports are scratch. -/
def frontendStore (input : List BSym) (dimension : ℕ)
    (suffix bitsRev status fuel data : List BSym) : Fin 32 → List BSym :=
  fun k => if k = 0 then input else if k = 1 then List.replicate dimension .one
    else if k = 2 then suffix else if k = 3 then bitsRev else if k = 4 then status
    else if k = 6 then fuel else if k = 7 then data else []

def frontendInputStore (input : List BSym) : Fin 32 → List BSym :=
  fun k => if k = 0 then input else []

def frontendHeaderStore (input : List BSym) (r : HeaderResult) : Fin 32 → List BSym :=
  frontendStore input r.dimension r.suffix [] (if r.found then [.one] else [])
    (List.replicate r.fuel .one) []

def frontendGraphStore (input : List BSym) (dimension : ℕ) (data : List BSym) : Fin 32 → List BSym :=
  frontendStore input dimension [] [] [.one] [] data

end TensorNP.Encoder
end


/- Inlined module: EmitterSpec -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.Encoder

/-- Backend dimension14, descending coordinates15/16/17, output5;
working18--31 start empty, and the validated frontend fields are preserved. -/
def emitterStore (input data : List BSym) (v N i j k : ℕ) (output : List BSym) : Fin 32 → List BSym :=
  fun l => if l = 5 then output else if l = 14 then List.replicate N .one
    else if l = 15 then List.replicate i .one else if l = 16 then List.replicate j .one
    else if l = 17 then List.replicate k .one else frontendGraphStore input v data l

end TensorNP.Encoder
end


/- Inlined module: EmitterLoops -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def chunkK (E : ℕ → ℕ → ℕ → List BSym) (i j count : ℕ) : List BSym :=
  (List.range count).flatMap (E i j)
def chunkJ (E : ℕ → ℕ → ℕ → List BSym) (N i count : ℕ) : List BSym :=
  (List.range count).flatMap (fun j => chunkK E i j N)
def chunkI (E : ℕ → ℕ → ℕ → List BSym) (N count : ℕ) : List BSym :=
  (List.range count).flatMap (fun i => chunkJ E N i N)

def emitKGuard (h : Fin 32 → Option BSym) : Bool := (h 17).isSome
def emitJGuard (h : Fin 32 → Option BSym) : Bool := (h 16).isSome
def emitIGuard (h : Fin 32 → Option BSym) : Bool := (h 15).isSome

def emitKLoop (entry : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .loop emitKGuard (.seq (popProg 17) entry)
def emitJLoop (entry : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .loop emitJGuard (.seq (popProg 16) (.seq (copyProg 14 17 20) (emitKLoop entry)))
def emitILoop (entry : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .loop emitIGuard (.seq (popProg 15) (.seq (copyProg 14 16 20) (emitJLoop entry)))
def denseEmitter (entry : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .seq (copyProg 14 15 20) (emitILoop entry)

lemma emitPopK (input data : List BSym) (v N i j k : ℕ) (tail : List BSym) :
    (popProg (17 : Fin 32)).Exec (emitterStore input data v N i j (k+1) tail)
      (emitterStore input data v N i j k tail) 1 := by
  have hu : Function.update (emitterStore input data v N i j (k+1) tail) 17
      ((emitterStore input data v N i j (k+1) tail) 17).tail = emitterStore input data v N i j k tail := by
    funext l
    fin_cases l <;> simp [emitterStore, frontendGraphStore, frontendStore, List.replicate_succ]
  simpa only [hu] using (stack_basic_macros (17 : Fin 32)
    (emitterStore input data v N i j (k+1) tail)).2.1

lemma emitPopJ (input data : List BSym) (v N i j : ℕ) (tail : List BSym) :
    (popProg (16 : Fin 32)).Exec (emitterStore input data v N i (j+1) 0 tail)
      (emitterStore input data v N i j 0 tail) 1 := by
  have hu : Function.update (emitterStore input data v N i (j+1) 0 tail) 16
      ((emitterStore input data v N i (j+1) 0 tail) 16).tail = emitterStore input data v N i j 0 tail := by
    funext l
    fin_cases l <;> simp [emitterStore, frontendGraphStore, frontendStore, List.replicate_succ]
  simpa only [hu] using (stack_basic_macros (16 : Fin 32)
    (emitterStore input data v N i (j+1) 0 tail)).2.1

lemma emitPopI (input data : List BSym) (v N i : ℕ) (tail : List BSym) :
    (popProg (15 : Fin 32)).Exec (emitterStore input data v N (i+1) 0 0 tail)
      (emitterStore input data v N i 0 0 tail) 1 := by
  have hu : Function.update (emitterStore input data v N (i+1) 0 0 tail) 15
      ((emitterStore input data v N (i+1) 0 0 tail) 15).tail = emitterStore input data v N i 0 0 tail := by
    funext l
    fin_cases l <;> simp [emitterStore, frontendGraphStore, frontendStore, List.replicate_succ]
  simpa only [hu] using (stack_basic_macros (15 : Fin 32)
    (emitterStore input data v N (i+1) 0 0 tail)).2.1

lemma emitCopyK (input data : List BSym) (v N i j : ℕ) (tail : List BSym) :
    (copyProg (14 : Fin 32) 17 20).Exec (emitterStore input data v N i j 0 tail)
      (emitterStore input data v N i j N tail) (6*N+3) := by
  have h := stack_copy (14 : Fin 32) 17 20 (by decide) (by decide) (by decide)
    (emitterStore input data v N i j 0 tail) (by rfl)
  have hu : Function.update (emitterStore input data v N i j 0 tail) 17
      (emitterStore input data v N i j 0 tail 14 ++ emitterStore input data v N i j 0 tail 17) =
      emitterStore input data v N i j N tail := by
    funext l
    fin_cases l <;> simp [emitterStore, frontendGraphStore, frontendStore]
  rw [hu] at h
  simpa [emitterStore] using h

lemma emitCopyJ (input data : List BSym) (v N i : ℕ) (tail : List BSym) :
    (copyProg (14 : Fin 32) 16 20).Exec (emitterStore input data v N i 0 0 tail)
      (emitterStore input data v N i N 0 tail) (6*N+3) := by
  have h := stack_copy (14 : Fin 32) 16 20 (by decide) (by decide) (by decide)
    (emitterStore input data v N i 0 0 tail) (by rfl)
  have hu : Function.update (emitterStore input data v N i 0 0 tail) 16
      (emitterStore input data v N i 0 0 tail 14 ++ emitterStore input data v N i 0 0 tail 16) =
      emitterStore input data v N i N 0 tail := by
    funext l
    fin_cases l <;> simp [emitterStore, frontendGraphStore, frontendStore]
  rw [hu] at h
  simpa [emitterStore] using h

lemma emitCopyI (input data : List BSym) (v N : ℕ) (tail : List BSym) :
    (copyProg (14 : Fin 32) 15 20).Exec (emitterStore input data v N 0 0 0 tail)
      (emitterStore input data v N N 0 0 tail) (6*N+3) := by
  have h := stack_copy (14 : Fin 32) 15 20 (by decide) (by decide) (by decide)
    (emitterStore input data v N 0 0 0 tail) (by rfl)
  have hu : Function.update (emitterStore input data v N 0 0 0 tail) 15
      (emitterStore input data v N 0 0 0 tail 14 ++ emitterStore input data v N 0 0 0 tail 15) =
      emitterStore input data v N N 0 0 tail := by
    funext l
    fin_cases l <;> simp [emitterStore, frontendGraphStore, frontendStore]
  rw [hu] at h
  simpa [emitterStore] using h

def denseEntrySpec (entry : StackProg (Fin 32) BSym) (E : ℕ → ℕ → ℕ → List BSym)
    (B : ℕ) (input data : List BSym) (v N : ℕ) : Prop :=
  ∀ (i j k : ℕ) (tail : List BSym), i < N → j < N → k < N →
    ∃ steps, entry.Exec (emitterStore input data v N i j k tail)
      (emitterStore input data v N i j k (E i j k ++ tail)) steps ∧ steps ≤ B

theorem emitKLoop_exec (entry : StackProg (Fin 32) BSym) (E : ℕ → ℕ → ℕ → List BSym)
    (B : ℕ) (input data : List BSym) (v N : ℕ) (hentry : denseEntrySpec entry E B input data v N) (i j count : ℕ)
    (hi : i < N) (hj : j < N) (hc : count ≤ N) (tail : List BSym) :
    ∃ steps, (emitKLoop entry).Exec (emitterStore input data v N i j count tail)
      (emitterStore input data v N i j 0 (chunkK E i j count ++ tail)) steps ∧
      steps ≤ count*(B+5)+1 := by
  induction count generalizing tail with
  | zero =>
      refine ⟨1, ?_, by simp⟩
      simpa [emitKLoop, chunkK] using (StackProg.Exec.loopFalse
        (p := .seq (popProg 17) entry) (test := emitKGuard)
        (s := emitterStore input data v N i j 0 tail) (by simp [emitKGuard, emitterStore]))
  | succ count ih =>
      obtain ⟨m, hm, hmB⟩ := hentry i j count tail hi hj (by omega)
      obtain ⟨r, hr, hrB⟩ := ih (by omega) (E i j count ++ tail)
      have hguard : emitKGuard (fun k => (emitterStore input data v N i j (count+1) tail k).head?) = true := by
        simp [emitKGuard, emitterStore, List.replicate_succ]
      have he := StackProg.Exec.loopTrue hguard
        (StackProg.Exec.seq (emitPopK input data v N i j count tail) hm) hr
      refine ⟨1 + (1 + 1 + m) + 1 + r, ?_, ?_⟩
      · simpa [emitKLoop, chunkK, List.range_succ, List.flatMap_append, List.append_assoc] using he
      · rw [Nat.add_mul]
        omega

theorem emitJLoop_exec (entry : StackProg (Fin 32) BSym) (E : ℕ → ℕ → ℕ → List BSym)
    (B : ℕ) (input data : List BSym) (v N : ℕ) (hentry : denseEntrySpec entry E B input data v N) (i count : ℕ)
    (hi : i < N) (hc : count ≤ N) (tail : List BSym) :
    ∃ steps, (emitJLoop entry).Exec (emitterStore input data v N i count 0 tail)
      (emitterStore input data v N i 0 0 (chunkJ E N i count ++ tail)) steps ∧
      steps ≤ count*(N*(B+5)+6*N+10)+1 := by
  induction count generalizing tail with
  | zero =>
      refine ⟨1, ?_, by simp⟩
      simpa [emitJLoop, chunkJ] using (StackProg.Exec.loopFalse
        (p := .seq (popProg 16) (.seq (copyProg 14 17 20) (emitKLoop entry))) (test := emitJGuard)
        (s := emitterStore input data v N i 0 0 tail) (by simp [emitJGuard, emitterStore]))
  | succ count ih =>
      obtain ⟨m, hm, hmB⟩ := emitKLoop_exec entry E B input data v N hentry i count N hi (by omega) le_rfl tail
      obtain ⟨r, hr, hrB⟩ := ih (by omega) (chunkK E i count N ++ tail)
      have hguard : emitJGuard (fun k => (emitterStore input data v N i (count+1) 0 tail k).head?) = true := by
        simp [emitJGuard, emitterStore, List.replicate_succ]
      have he := StackProg.Exec.loopTrue hguard
        (StackProg.Exec.seq (emitPopJ input data v N i count tail)
          (StackProg.Exec.seq (emitCopyK input data v N i count tail) hm)) hr
      refine ⟨1 + (1 + 1 + ((6*N+3) + 1 + m)) + 1 + r, ?_, ?_⟩
      · simpa [emitJLoop, chunkJ, List.range_succ, List.flatMap_append, List.append_assoc] using he
      · rw [Nat.add_mul]
        omega

theorem emitILoop_exec (entry : StackProg (Fin 32) BSym) (E : ℕ → ℕ → ℕ → List BSym)
    (B : ℕ) (input data : List BSym) (v N : ℕ) (hentry : denseEntrySpec entry E B input data v N) (count : ℕ)
    (hc : count ≤ N) (tail : List BSym) :
    ∃ steps, (emitILoop entry).Exec (emitterStore input data v N count 0 0 tail)
      (emitterStore input data v N 0 0 0 (chunkI E N count ++ tail)) steps ∧
      steps ≤ count*(N*(N*(B+5)+6*N+10)+6*N+10)+1 := by
  induction count generalizing tail with
  | zero =>
      refine ⟨1, ?_, by simp⟩
      simpa [emitILoop, chunkI] using (StackProg.Exec.loopFalse
        (p := .seq (popProg 15) (.seq (copyProg 14 16 20) (emitJLoop entry))) (test := emitIGuard)
        (s := emitterStore input data v N 0 0 0 tail) (by simp [emitIGuard, emitterStore]))
  | succ count ih =>
      obtain ⟨m, hm, hmB⟩ := emitJLoop_exec entry E B input data v N hentry count N (by omega) le_rfl tail
      obtain ⟨r, hr, hrB⟩ := ih (by omega) (chunkJ E N count N ++ tail)
      have hguard : emitIGuard (fun k => (emitterStore input data v N (count+1) 0 0 tail k).head?) = true := by
        simp [emitIGuard, emitterStore, List.replicate_succ]
      have he := StackProg.Exec.loopTrue hguard
        (StackProg.Exec.seq (emitPopI input data v N count tail)
          (StackProg.Exec.seq (emitCopyJ input data v N count tail) hm)) hr
      refine ⟨1 + (1 + 1 + ((6*N+3) + 1 + m)) + 1 + r, ?_, ?_⟩
      · simpa [emitILoop, chunkI, List.range_succ, List.flatMap_append, List.append_assoc] using he
      · rw [Nat.add_mul]
        omega

theorem dense_emitter_source (entry : StackProg (Fin 32) BSym) :
    ∃ p : StackProg (Fin 32) BSym,
      ∀ (E : ℕ → ℕ → ℕ → List BSym) (B : ℕ) (input data : List BSym) (v N : ℕ),
      denseEntrySpec entry E B input data v N → ∀ (tail : List BSym), ∃ steps,
        p.Exec (emitterStore input data v N 0 0 0 tail)
          (emitterStore input data v N 0 0 0 (chunkI E N N ++ tail)) steps ∧
        steps ≤ (B+100)*(N+1)^4 := by
  refine ⟨denseEmitter entry, ?_⟩
  intro E B input data v N hentry tail
  obtain ⟨m, hm, hmB⟩ := emitILoop_exec entry E B input data v N hentry N le_rfl tail
  have he := StackProg.Exec.seq (emitCopyI input data v N tail) hm
  refine ⟨(6*N+3)+1+m, he, ?_⟩
  nlinarith [Nat.zero_le (B*N^4), Nat.zero_le (B*N^3), Nat.zero_le (B*N^2),
    Nat.zero_le (B*N), Nat.zero_le (N^4), Nat.zero_le (N^3), Nat.zero_le (N^2)]

end TensorNP.Encoder
end


/- Inlined module: TensorWord -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Eigen

namespace TensorNP.Encoder

lemma rangeFlatMap_ofFn {α : Type} (N : ℕ) (f : ℕ → List α) (g : Fin N → List α)
    (h : ∀ i : Fin N, f i.val = g i) :
    (List.range N).flatMap f = (List.ofFn g).flatten := by
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map, List.ofFn_eq_map]
  congr 1
  funext i
  exact h i

theorem dense_tensor_code {N : ℕ} (A : Fin N → Fin N → Fin N → ℚ)
    (E : ℕ → ℕ → ℕ → List BSym)
    (h : ∀ i j k : Fin N, E i.val j.val k.val = encRat (A i j k)) :
    encNat N ++ chunkI E N N = tensorCode A := by
  unfold tensorCode chunkI
  congr 1
  apply rangeFlatMap_ofFn
  intro i
  unfold chunkJ
  apply rangeFlatMap_ofFn
  intro j
  unfold chunkK
  apply rangeFlatMap_ofFn
  intro k
  exact h i j k

lemma splitCounts_le (m n bound : ℕ) (A : ℕ → ℕ → ℕ → ℕ × ℕ)
    (hA : ∀ q a b, (A q a b).1 + (A q a b).2 ≤ bound) (q a b : ℕ) :
    (splitCounts m n A q a b).1 + (splitCounts m n A q a b).2 ≤ bound := by
  unfold splitCounts
  split_ifs
  all_goals try dsimp only [swapCounts]
  all_goals first | exact hA _ _ _ | (rw [Nat.add_comm]; exact hA _ _ _) | omega

theorem tensorCounts_le (v : ℕ) (data : List BSym) (i j k : ℕ) :
    (tensorCounts v data i j k).1 + (tensorCounts v data i j k).2 ≤ 3*v+2 := by
  have hA : ∀ q a b, (colorCounts v data q a b).1 + (colorCounts v data q a b).2 ≤ 3*v+2 := by
    intro q a b
    exact rawCounts_le v data (q/v) (q%v) a b
  have hs := splitCounts_le (4*v) (2*v+1) (3*v+2) (colorCounts v data) hA k i j
  unfold tensorCounts
  split_ifs <;> simp_all

theorem raw_tensor_code {v : ℕ} (G : SimpleGraph (Fin v)) :
    encNat (colorSize v) ++
      chunkI (fun i j k => encRat ((rawTensorEntry v (graphData G) i j k : ℤ) : ℚ))
        (colorSize v) (colorSize v) = tensorCode (colorTensor G) := by
  apply dense_tensor_code
  intro i j k
  rw [rawTensorEntry_cast]

end TensorNP.Encoder
end


/- Inlined module: EncoderValue -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen
namespace TensorNP.Encoder

def denseWord (v : ℕ) (data : List BSym) : List BSym :=
  encNat (colorSize v) ++ chunkI
    (fun i j k => encRat ((rawTensorEntry v data i j k : ℤ) : ℚ)) (colorSize v) (colorSize v)

/-- Total value function: the same bounded parser used by the executable frontend. -/
def eigenEncoderValue (input : List BSym) : List BSym :=
  let r := boundedHeader 0 (input.length+1) input
  if graphInputValid input then
    match parseBits (r.dimension*r.dimension) r.suffix with
    | none => []
    | some (bs, _) => denseWord r.dimension (bs.map boolSym)
  else []

theorem eigenEncoderValue_graphCode {v : ℕ} (G : SimpleGraph (Fin v)) :
    eigenEncoderValue (graphCode G) = tensorCode (colorTensor G) := by
  have hc := canonical_front_packet G (graphCode G) rfl
  simp only [eigenEncoderValue, graphInputValid_graphCode, ↓reduceIte]
  rw [hc.2.2.1, hc.2.1]
  exact raw_tensor_code G

theorem eigenEncoderValue_invalid (input : List BSym)
    (h : ¬∃ (v : ℕ) (G : SimpleGraph (Fin v)), input=graphCode G) :
    eigenEncoderValue input=[] := by
  simp [eigenEncoderValue, graphInputValid_invalid input h]

end TensorNP.Encoder
end


/- Inlined module: Header32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def headerPorts32 : Fin 12 ↪ Fin 32 := ⟨![1, 7, 8, 9, 10, 0, 2, 6, 4, 11, 12, 13], by decide⟩

def headerDecode32 (l : Fin 32) : Option (Fin 12) :=
  if l = 1 then some 0 else if l = 7 then some 1 else if l = 8 then some 2
  else if l = 9 then some 3 else if l = 10 then some 4 else if l = 0 then some 5
  else if l = 2 then some 6 else if l = 6 then some 7 else if l = 4 then some 8
  else if l = 11 then some 9 else if l = 12 then some 10 else if l = 13 then some 11 else none

lemma headerDecode32_spec (l : Fin 32) (k : Fin 12) :
    headerDecode32 l = some k ↔ headerPorts32 k = l := by
  fin_cases l <;> fin_cases k <;> decide

lemma headerFrontend_project (input : List BSym) :
    StackProgPortLift.project headerPorts32 (frontendInputStore input) = headerInputStore input := by
  funext k
  fin_cases k <;> rfl

private lemma header_write_at (t : Fin 12 → List BSym) (s : Fin 32 → List BSym) (k : Fin 12) :
    StackProgPortLift.write headerPorts32 t s (headerPorts32 k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := headerPorts32.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma headerFrontend_write (input : List BSym) (r : HeaderResult) :
    StackProgPortLift.write headerPorts32 (headerResultStore r input) (frontendInputStore input) =
      frontendHeaderStore input r := by
  classical
  funext l
  by_cases hl : ∃ k, headerPorts32 k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [header_write_at]
    fin_cases k <;> rfl
  · have h0 : l ≠ 0 := by
      intro he
      apply hl
      exact ⟨5, he.symm⟩
    have h1 : l ≠ 1 := by
      intro he
      apply hl
      exact ⟨0, he.symm⟩
    have h2 : l ≠ 2 := by
      intro he
      apply hl
      exact ⟨6, he.symm⟩
    have h4 : l ≠ 4 := by
      intro he
      apply hl
      exact ⟨8, he.symm⟩
    have h6 : l ≠ 6 := by
      intro he
      apply hl
      exact ⟨7, he.symm⟩
    simp [StackProgPortLift.write, hl, frontendInputStore, frontendHeaderStore, frontendStore,
      h0, h1, h2, h4, h6]

theorem frontend_header_source : ∃ (p : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ input : List BSym, ∃ steps,
      p.Exec (frontendInputStore input)
        (frontendHeaderStore input (boundedHeader 0 (input.length + 1) input)) steps ∧
      steps ≤ C * (input.length + 2)^3 := by
  obtain ⟨p, C, hp⟩ := header_parser_source
  refine ⟨StackProgPortLift.liftProgC headerPorts32 headerDecode32 p, C, ?_⟩
  intro input
  obtain ⟨steps, he, hb⟩ := hp input
  refine ⟨steps, ?_, hb⟩
  have he' := StackProgPortLift.liftProgC_exec headerPorts32 headerDecode32
    headerDecode32_spec he (frontendInputStore input) (headerFrontend_project input)
  rw [headerFrontend_write] at he'
  exact he'

end TensorNP.Encoder
end


/- Inlined module: UnarySquare -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def squareStore (n out count : ℕ) : Fin 4 → List BSym :=
  fun k => if k = 0 then List.replicate n .one
    else if k = 1 then List.replicate out .one
    else if k = 2 then List.replicate count .one else []

def squareBody : StackProg (Fin 4) BSym := .seq (popProg 2) (copyProg 0 1 3)
def squareLoop : StackProg (Fin 4) BSym := .loop (fun h => (h 2).isSome) squareBody
def squareProg : StackProg (Fin 4) BSym := .seq (copyProg 0 2 3) squareLoop

lemma squarePop (n out count : ℕ) :
    (popProg (2 : Fin 4)).Exec (squareStore n out (count + 1)) (squareStore n out count) 1 := by
  have he : StackProg.applyAct (fun (_ : Fin 4 → Option BSym) (k : Fin 4) => if k = 2 then .pop else .keep)
      (squareStore n out (count + 1)) = squareStore n out count := by
    funext k
    fin_cases k <;> simp [StackProg.applyAct, squareStore, StackAct.apply, List.replicate_succ]
  simpa only [popProg, he] using StackProg.Exec.act
    (fun (_ : Fin 4 → Option BSym) (k : Fin 4) => if k = 2 then .pop else .keep) (squareStore n out (count + 1))

lemma squareCopyOutput (n out count : ℕ) :
    (copyProg (0 : Fin 4) 1 3).Exec (squareStore n out count)
      (squareStore n (n + out) count) (6 * n + 3) := by
  have h := stack_copy (0 : Fin 4) 1 3 (by decide) (by decide) (by decide)
    (squareStore n out count) (by simp [squareStore])
  have hu : Function.update (squareStore n out count) 1
      (squareStore n out count 0 ++ squareStore n out count 1) =
      squareStore n (n + out) count := by
    funext k
    fin_cases k <;> simp [squareStore]
  rw [hu] at h
  simpa [squareStore] using h

lemma squareCopyCounter (n : ℕ) :
    (copyProg (0 : Fin 4) 2 3).Exec (squareStore n 0 0) (squareStore n 0 n) (6 * n + 3) := by
  have h := stack_copy (0 : Fin 4) 2 3 (by decide) (by decide) (by decide)
    (squareStore n 0 0) (by simp [squareStore])
  have hu : Function.update (squareStore n 0 0) 2
      (squareStore n 0 0 0 ++ squareStore n 0 0 2) = squareStore n 0 n := by
    funext k
    fin_cases k <;> simp [squareStore]
  rw [hu] at h
  simpa [squareStore] using h

lemma squareLoop_exec (n count out : ℕ) :
    squareLoop.Exec (squareStore n out count) (squareStore n (out + count * n) 0)
      ((6 * n + 7) * count + 1) := by
  induction count generalizing out with
  | zero =>
      simpa [squareLoop] using (StackProg.Exec.loopFalse
        (test := fun h : Fin 4 → Option BSym => (h 2).isSome)
        (p := squareBody) (s := squareStore n out 0) (by simp [squareStore]))
  | succ count ih =>
      have hb : squareBody.Exec (squareStore n out (count + 1))
          (squareStore n (n + out) count) (6 * n + 5) := by
        have he := StackProg.Exec.seq (squarePop n out count) (squareCopyOutput n out count)
        convert he using 1 <;> first | rfl | omega
      have hg : (fun h : Fin 4 → Option BSym => (h 2).isSome)
          (fun k => (squareStore n out (count + 1) k).head?) = true := by
        simp [squareStore, List.replicate_succ]
      have he := StackProg.Exec.loopTrue hg hb (ih (n + out))
      have hout : n + out + count * n = out + (count + 1) * n := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      have hsteps : 1 + (6 * n + 5) + 1 + ((6 * n + 7) * count + 1) =
          (6 * n + 7) * (count + 1) + 1 := by
        rw [Nat.mul_add]
        omega
      simpa only [squareLoop, ← hout, ← hsteps] using he

theorem unary_square_machine : ∃ p : StackProg (Fin 4) BSym, ∀ n : ℕ,
    p.Exec (squareStore n 0 0) (squareStore n (n * n) 0) (6 * n * n + 13 * n + 5) := by
  refine ⟨squareProg, ?_⟩
  intro n
  have he := StackProg.Exec.seq (squareCopyCounter n) (squareLoop_exec n n 0)
  convert he using 1 <;> simp [squareProg, Nat.add_mul]
  all_goals omega

end TensorNP.Encoder
end


/- Inlined module: Packet32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def packetSquarePorts : Fin 4 ↪ Fin 32 := ⟨![1, 6, 7, 8], by decide⟩
def packetBitPorts : Fin 4 ↪ Fin 32 := ⟨![2, 6, 3, 4], by decide⟩

def packetSquareDecode (l : Fin 32) : Option (Fin 4) :=
  if l = 1 then some 0 else if l = 6 then some 1 else if l = 7 then some 2
    else if l = 8 then some 3 else none

def packetBitDecode (l : Fin 32) : Option (Fin 4) :=
  if l = 2 then some 0 else if l = 6 then some 1 else if l = 3 then some 2
    else if l = 4 then some 3 else none

lemma packetSquareDecode_spec (l : Fin 32) (k : Fin 4) :
    packetSquareDecode l = some k ↔ packetSquarePorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

lemma packetBitDecode_spec (l : Fin 32) (k : Fin 4) :
    packetBitDecode l = some k ↔ packetBitPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

private lemma packetWrite_at (r : Fin 4 ↪ Fin 32) (t : Fin 4 → List BSym)
    (s : Fin 32 → List BSym) (k : Fin 4) :
    StackProgPortLift.write r t s (r k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := r.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma packetSquare_project (input suffix : List BSym) (n out : ℕ) :
    StackProgPortLift.project packetSquarePorts
      (frontendStore input n suffix [] [.one] (List.replicate out .one) []) = squareStore n out 0 := by
  funext k
  fin_cases k <;> rfl

lemma packetSquare_write (input suffix : List BSym) (n : ℕ) :
    StackProgPortLift.write packetSquarePorts (squareStore n (n*n) 0)
      (frontendStore input n suffix [] [.one] [] []) =
      frontendStore input n suffix [] [.one] (List.replicate (n*n) .one) [] := by
  classical
  funext l
  by_cases hl : ∃ k, packetSquarePorts k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [packetWrite_at]
    exact (congrFun (packetSquare_project input suffix n (n*n)) k).symm
  · have h6 : l ≠ 6 := by
      intro h
      apply hl
      exact ⟨1, h.symm⟩
    simp [StackProgPortLift.write, hl, frontendStore, h6]

lemma packetBit_project (input suffix fuel : List BSym) (n : ℕ) :
    StackProgPortLift.project packetBitPorts (frontendStore input n suffix [] [] fuel []) =
      bitParserStore suffix fuel [] [] := by
  funext k
  fin_cases k <;> rfl

lemma packetBit_write (input suffix tail bits : List BSym) (n : ℕ) :
    StackProgPortLift.write packetBitPorts (bitParserStore tail [] bits [.one])
      (frontendStore input n suffix [] [] (List.replicate (n*n) .one) []) =
      frontendStore input n tail bits [.one] [] [] := by
  classical
  funext l
  by_cases hl : ∃ k, packetBitPorts k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [packetWrite_at]
    fin_cases k <;> rfl
  · have h2 : l ≠ 2 := by intro h; apply hl; exact ⟨0, h.symm⟩
    have h6 : l ≠ 6 := by intro h; apply hl; exact ⟨1, h.symm⟩
    have h3 : l ≠ 3 := by intro h; apply hl; exact ⟨2, h.symm⟩
    have h4 : l ≠ 4 := by intro h; apply hl; exact ⟨3, h.symm⟩
    simp [StackProgPortLift.write, hl, frontendStore, h2, h6, h3, h4]

lemma packetBit_write_status (s : Fin 4 → List BSym) (base : Fin 32 → List BSym) :
    StackProgPortLift.write packetBitPorts s base 4 = s 3 := by
  exact packetWrite_at packetBitPorts s base 3

lemma packetBit_write_output (s : Fin 4 → List BSym) (base : Fin 32 → List BSym) :
    StackProgPortLift.write packetBitPorts s base 5 = base 5 := by
  classical
  have hn : ¬ ∃ k, packetBitPorts k = 5 := by decide
  simp [StackProgPortLift.write, hn]

lemma packetPopStatus_exec (input suffix : List BSym) (n : ℕ) :
    (popProg (4 : Fin 32)).Exec
      (frontendStore input n suffix [] [.one] (List.replicate (n*n) .one) [])
      (frontendStore input n suffix [] [] (List.replicate (n*n) .one) []) 1 := by
  have hu : Function.update (frontendStore input n suffix [] [.one] (List.replicate (n*n) .one) []) 4
      ((frontendStore input n suffix [] [.one] (List.replicate (n*n) .one) []) 4).tail =
      frontendStore input n suffix [] [] (List.replicate (n*n) .one) [] := by
    funext k
    fin_cases k <;> simp [frontendStore]
  simpa only [hu] using (stack_basic_macros (4 : Fin 32)
    (frontendStore input n suffix [] [.one] (List.replicate (n*n) .one) [])).2.1

theorem frontend_packet_source : ∃ p : StackProg (Fin 32) BSym,
    ∀ (input : List BSym) (n : ℕ) (suffix : List BSym), ∃ (s : Fin 32 → List BSym) (steps : ℕ),
      p.Exec (frontendStore input n suffix [] [.one] [] []) s steps ∧
      steps ≤ 100*(n+1)^2 ∧
      (∀ (bs : List Bool) (tail : List BSym), parseBits (n*n) suffix = some (bs, tail) →
        s = frontendStore input n tail ((bs.map boolSym).reverse) [.one] [] []) ∧
      (parseBits (n*n) suffix = none → s 4 = [.zero] ∧ s 5 = []) := by
  obtain ⟨ps, hs⟩ := unary_square_machine
  obtain ⟨pb, hb⟩ := bit_parser_machine
  refine ⟨.seq (StackProgPortLift.liftProgC packetSquarePorts packetSquareDecode ps)
    (.seq (popProg 4) (StackProgPortLift.liftProgC packetBitPorts packetBitDecode pb)), ?_⟩
  intro input n suffix
  have hsq := StackProgPortLift.liftProgC_exec packetSquarePorts packetSquareDecode
    packetSquareDecode_spec (hs n) (frontendStore input n suffix [] [.one] [] [])
    (by simpa using packetSquare_project input suffix n 0)
  rw [packetSquare_write] at hsq
  obtain ⟨t, m, hbit, hm, hsuccess, hfailure⟩ := hb (n*n) suffix
  have hbp := StackProgPortLift.liftProgC_exec packetBitPorts packetBitDecode
    packetBitDecode_spec hbit
    (frontendStore input n suffix [] [] (List.replicate (n*n) .one) [])
    (packetBit_project input suffix (List.replicate (n*n) .one) n)
  have hex := StackProg.Exec.seq hsq (StackProg.Exec.seq (packetPopStatus_exec input suffix n) hbp)
  refine ⟨_, _, hex, ?_, ?_, ?_⟩
  · nlinarith
  · intro bs tail h
    rw [hsuccess bs tail h]
    exact packetBit_write input suffix tail ((bs.map boolSym).reverse) n
  · intro h
    constructor
    · rw [packetBit_write_status, hfailure h]
    · rw [packetBit_write_output]
      rfl

end TensorNP.Encoder
end


/- Inlined module: Matrix32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def matrix32Ports : Fin 12 ↪ Fin 32 := ⟨![7,1,6,8,9,10,11,12,4,13,14,15], by decide⟩

def matrix32Decode (l : Fin 32) : Option (Fin 12) :=
  if l = 7 then some 0 else if l = 1 then some 1 else if l = 6 then some 2
  else if l = 8 then some 3 else if l = 9 then some 4 else if l = 10 then some 5
  else if l = 11 then some 6 else if l = 12 then some 7 else if l = 4 then some 8
  else if l = 13 then some 9 else if l = 14 then some 10 else if l = 15 then some 11 else none

lemma matrix32Decode_spec (l : Fin 32) (k : Fin 12) :
    matrix32Decode l = some k ↔ matrix32Ports k = l := by
  fin_cases l <;> fin_cases k <;> decide

private lemma matrix32Write_at (t : Fin 12 → List BSym) (s : Fin 32 → List BSym) (k : Fin 12) :
    StackProgPortLift.write matrix32Ports t s (matrix32Ports k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := matrix32Ports.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma matrix32_project (input data : List BSym) (n : ℕ) (good : Bool) :
    StackProgPortLift.project matrix32Ports
      (frontendStore input n [] [] (if good then [] else [.zero]) [] data) =
      checkerStore n 0 0 data good := by
  funext k
  fin_cases k <;> rfl

lemma matrix32_write (input data : List BSym) (n : ℕ) (good : Bool) :
    StackProgPortLift.write matrix32Ports (checkerStore n 0 0 data good)
      (frontendStore input n [] [] [] [] data) =
      frontendStore input n [] [] (if good then [] else [.zero]) [] data := by
  classical
  funext l
  by_cases hl : ∃ k, matrix32Ports k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [matrix32Write_at]
    exact (congrFun (matrix32_project input data n good) k).symm
  · have h4 : l ≠ 4 := by intro h; apply hl; exact ⟨8, h.symm⟩
    simp [StackProgPortLift.write, hl, frontendStore, h4]

def matrix32Targets (k : Fin 32) : Bool := decide (k = 7)

def matrix32Normalize (h : Fin 32 → Option BSym) (k : Fin 32) : StackAct BSym :=
  if k = 4 ∧ h 4 = none then .push .one else .keep

lemma matrix32Transfer_exec (input data : List BSym) (n : ℕ) :
    (transferProg (3 : Fin 32) matrix32Targets).Exec
      (frontendStore input n [] data.reverse [.one] [] [])
      (frontendStore input n [] [] [.one] [] data) (3*data.length+1) := by
  have h := stack_transfer (3 : Fin 32) matrix32Targets
    (frontendStore input n [] data.reverse [.one] [] [])
  have hu : transferStore (3 : Fin 32) matrix32Targets
      (frontendStore input n [] data.reverse [.one] [] []) =
      frontendStore input n [] [] [.one] [] data := by
    funext k
    fin_cases k <;> simp [transferStore, matrix32Targets, frontendStore]
  rw [hu] at h
  simpa [frontendStore] using h

lemma matrix32Pop_exec (input data : List BSym) (n : ℕ) :
    (popProg (4 : Fin 32)).Exec (frontendStore input n [] [] [.one] [] data)
      (frontendStore input n [] [] [] [] data) 1 := by
  have hu : Function.update (frontendStore input n [] [] [.one] [] data) 4
      ((frontendStore input n [] [] [.one] [] data) 4).tail =
      frontendStore input n [] [] [] [] data := by
    funext k
    fin_cases k <;> simp [frontendStore]
  simpa only [hu] using (stack_basic_macros (4 : Fin 32)
    (frontendStore input n [] [] [.one] [] data)).2.1

lemma matrix32Normalize_exec (input data : List BSym) (n : ℕ) (good : Bool) :
    (StackProg.act matrix32Normalize).Exec
      (frontendStore input n [] [] (if good then [] else [.zero]) [] data)
      (frontendStore input n [] [] [if good then .one else .zero] [] data) 1 := by
  have hu : StackProg.applyAct matrix32Normalize
      (frontendStore input n [] [] (if good then [] else [.zero]) [] data) =
      frontendStore input n [] [] [if good then .one else .zero] [] data := by
    cases good <;> funext k <;> fin_cases k <;> rfl
  simpa only [hu] using StackProg.Exec.act matrix32Normalize
    (frontendStore input n [] [] (if good then [] else [.zero]) [] data)

theorem frontend_matrix_source : ∃ p : StackProg (Fin 32) BSym,
    ∀ (input : List BSym) (n : ℕ) (bs : List Bool), bs.length = n*n → ∃ steps,
      p.Exec (frontendStore input n [] ((bs.map boolSym).reverse) [.one] [] [])
        (frontendStore input n [] [] [if decide (ValidMatrix n bs) then BSym.one else .zero]
          [] (bs.map boolSym)) steps ∧
      steps ≤ 1100*(n+1)^4 := by
  obtain ⟨pc, hc⟩ := matrix_checker_source
  refine ⟨.seq (transferProg 3 matrix32Targets)
    (.seq (popProg 4) (.seq (StackProgPortLift.liftProgC matrix32Ports matrix32Decode pc)
      (.act matrix32Normalize))), ?_⟩
  intro input n bs hlen
  have hlen' : (bs.map boolSym).length = n*n := by simpa using hlen
  obtain ⟨m, hm, hmB⟩ := hc n (bs.map boolSym) true hlen'
  have hlift := StackProgPortLift.liftProgC_exec matrix32Ports matrix32Decode matrix32Decode_spec
    hm (frontendStore input n [] [] [] [] (bs.map boolSym))
    (by simpa using matrix32_project input (bs.map boolSym) n true)
  rw [matrix32_write] at hlift
  have he := StackProg.Exec.seq (matrix32Transfer_exec input (bs.map boolSym) n)
    (StackProg.Exec.seq (matrix32Pop_exec input (bs.map boolSym) n)
      (StackProg.Exec.seq hlift (matrix32Normalize_exec input (bs.map boolSym) n
        (true && matrixCheckPrefix n (bs.map boolSym) n))))
  have hflag : matrixCheckPrefix n (bs.map boolSym) n = decide (ValidMatrix n bs) := by
    have hiff := matrixCheckPrefix_valid n bs hlen
    cases h : matrixCheckPrefix n (bs.map boolSym) n <;> simp_all
  rw [Bool.true_and, hflag] at he
  refine ⟨_, he, ?_⟩
  have hpow : (n+1)^2 ≤ (n+1)^4 := pow_le_pow_right₀ (by omega) (by omega)
  have hsquare : n*n ≤ (n+1)^2 := by nlinarith
  have hquart : n*n ≤ (n+1)^4 := le_trans hsquare hpow
  have hone : 1 ≤ (n+1)^4 := Nat.one_le_pow 4 (n+1) (by omega)
  simp only [List.length_map, hlen]
  omega

end TensorNP.Encoder
end


/- Inlined module: Frontend -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def frontendHeaderGuard (h : Fin 32 → Option BSym) : Bool := h 4 == some .one

def frontendPacketGuard (h : Fin 32 → Option BSym) : Bool :=
  (h 4 == some .one) && (h 2).isNone

def frontendReject : StackProg (Fin 32) BSym := .seq (popProg 4) (pushProg 4 .zero)

def frontendProgram (header packet matrix : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .seq header (.branch frontendHeaderGuard
    (.seq (clearProg 6) (.seq packet (.branch frontendPacketGuard matrix frontendReject))) frontendReject)

def FrontCorrect (input : List BSym) (s : Fin 32 → List BSym) : Prop :=
  (∀ (v : ℕ) (G : SimpleGraph (Fin v)), input = TensorNP.Eigen.graphCode G →
    s = frontendGraphStore input v ((graphBits G).map boolSym)) ∧
  ((¬ ∃ (v : ℕ) (G : SimpleGraph (Fin v)), input = TensorNP.Eigen.graphCode G) →
    s 4 = [.zero] ∧ s 5 = [])

theorem frontendReject_exec (s : Fin 32 → List BSym) (hstatus : (s 4).tail = []) :
    frontendReject.Exec s (Function.update s 4 [.zero]) 3 := by
  have hp := (stack_basic_macros (4 : Fin 32) s).2.1
  have hq := (stack_basic_macros (4 : Fin 32) (Function.update s 4 (s 4).tail)).1 BSym.zero
  have he := StackProg.Exec.seq hp hq
  have heq : Function.update (Function.update s 4 (s 4).tail) 4
      (.zero :: (Function.update s 4 (s 4).tail) 4) = Function.update s 4 [.zero] := by
    simp [hstatus]
  simpa only [frontendReject, heq] using he

theorem frontendClearFuel_exec (input : List BSym) (n : ℕ)
    (suffix bits status fuel data : List BSym) :
    (clearProg (6 : Fin 32)).Exec (frontendStore input n suffix bits status fuel data)
      (frontendStore input n suffix bits status [] data) (3*fuel.length+1) := by
  have heq : Function.update (frontendStore input n suffix bits status fuel data) 6 [] =
      frontendStore input n suffix bits status [] data := by
    funext k
    fin_cases k <;> simp [frontendStore]
  have hc := (stack_basic_macros (6 : Fin 32) (frontendStore input n suffix bits status fuel data)).2.2
  rw [heq] at hc
  simpa [frontendStore] using hc

theorem frontendHeaderGuard_store (input : List BSym) (r : HeaderResult) :
    frontendHeaderGuard (fun k => (frontendHeaderStore input r k).head?) = r.found := by
  cases hf : r.found <;> simp [frontendHeaderGuard, frontendHeaderStore, frontendStore, hf]

theorem frontend_budget (C L head clear packet matrix : ℕ)
    (hh : head ≤ C*(L+2)^3) (hc : clear ≤ 3*(L+1)+1)
    (hp : packet ≤ 100*(L+1)^2) (hm : matrix ≤ 1100*(L+1)^4) :
    head+clear+packet+matrix+20 ≤ (C+5000)*(L+2)^5 := by
  have h1 : L+2 ≤ (L+2)^5 := Nat.le_self_pow (by decide) _
  have h3 : (L+2)^3 ≤ (L+2)^5 := pow_le_pow_right₀ (by omega) (by decide)
  have h2 : (L+1)^2 ≤ (L+2)^5 :=
    (Nat.pow_le_pow_left (by omega : L+1 ≤ L+2) 2).trans
      (pow_le_pow_right₀ (by omega) (by decide))
  have h4 : (L+1)^4 ≤ (L+2)^5 :=
    (Nat.pow_le_pow_left (by omega : L+1 ≤ L+2) 4).trans
      (pow_le_pow_right₀ (by omega) (by decide))
  have hh' := hh.trans (Nat.mul_le_mul_left C h3)
  have hp' := hp.trans (Nat.mul_le_mul_left 100 h2)
  have hm' := hm.trans (Nat.mul_le_mul_left 1100 h4)
  rw [Nat.add_mul]
  omega

theorem graph_frontend_source : ∃ (p : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ input : List BSym, ∃ (s : Fin 32 → List BSym) (steps : ℕ),
      p.Exec (frontendInputStore input) s steps ∧ steps ≤ C*(input.length+2)^5 ∧ FrontCorrect input s := by
  obtain ⟨ph, Ch, hph⟩ := frontend_header_source
  obtain ⟨pp, hpp⟩ := frontend_packet_source
  obtain ⟨pm, hpm⟩ := frontend_matrix_source
  refine ⟨frontendProgram ph pp pm, Ch+5000, fun input => ?_⟩
  let r := boundedHeader 0 (input.length+1) input
  obtain ⟨h, hhead, hh⟩ := hph input
  by_cases hf : r.found = true
  · have hclear : (clearProg (6 : Fin 32)).Exec (frontendHeaderStore input r)
        (frontendStore input r.dimension r.suffix [] [.one] [] []) (3*r.fuel+1) := by
      simpa [frontendHeaderStore, hf] using
        frontendClearFuel_exec input r.dimension r.suffix [] [.one] (List.replicate r.fuel .one) []
    obtain ⟨s, u, hpacket, hu, hps, hpf⟩ := hpp input r.dimension r.suffix
    have hn : r.dimension ≤ input.length := boundedHeader_dimension_le input hf
    have hrf : r.fuel ≤ input.length+1 := boundedHeader_fuel_le 0 (input.length+1) input
    have hu' : u ≤ 100*(input.length+1)^2 :=
      hu.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (by omega) 2))
    cases hp0 : parseBits (r.dimension*r.dimension) r.suffix with
    | none =>
        have hfail := hpf hp0
        have hreject := frontendReject_exec s (by simp [hfail.1])
        have hinner := StackProg.Exec.branchFalse (test := frontendPacketGuard)
          (p := pm) (by simp [frontendPacketGuard, hfail.1]) hreject
        have houter := StackProg.Exec.branchTrue (test := frontendHeaderGuard)
          (q := frontendReject) (by rw [frontendHeaderGuard_store, hf])
          (StackProg.Exec.seq hclear (StackProg.Exec.seq hpacket hinner))
        have hex := StackProg.Exec.seq hhead houter
        refine ⟨_, _, hex, ?_, ?_, ?_⟩
        · have hbudget := frontend_budget Ch input.length h (3*r.fuel+1) u 0 hh
            (by omega) hu' (by omega)
          omega
        · intro vertex G hinput
          have hc := canonical_front_packet G input hinput
          have hp := hc.2.2.1
          rw [hp0] at hp
          contradiction
        · intro _
          simp [hfail.2]
    | some pair =>
        rcases pair with ⟨bs, tail⟩
        rw [hps bs tail hp0] at hpacket
        by_cases ht : tail = []
        · subst tail
          have hlen : bs.length = r.dimension*r.dimension := (parseBits_sound _ _ _ _ hp0).1
          obtain ⟨v, hmatrix, hv⟩ := hpm input r.dimension bs hlen
          have hinner := StackProg.Exec.branchTrue (test := frontendPacketGuard)
            (q := frontendReject) (by simp [frontendPacketGuard, frontendStore]) hmatrix
          have houter := StackProg.Exec.branchTrue (test := frontendHeaderGuard)
            (q := frontendReject) (by rw [frontendHeaderGuard_store, hf])
            (StackProg.Exec.seq hclear (StackProg.Exec.seq hpacket hinner))
          have hex := StackProg.Exec.seq hhead houter
          refine ⟨_, _, hex, ?_, ?_, ?_⟩
          · have hv' : v ≤ 1100*(input.length+1)^4 :=
              hv.trans (Nat.mul_le_mul_left 1100 (Nat.pow_le_pow_left (by omega) 4))
            have hb := frontend_budget Ch input.length h (3*r.fuel+1) u v hh (by omega) hu' hv'
            omega
          · intro vertex G hinput
            have hc := canonical_front_packet G input hinput
            have hpEq : (bs, []) = (graphBits G, []) := Option.some.inj (hp0.symm.trans hc.2.2.1)
            have hbs : bs = graphBits G := congrArg Prod.fst hpEq
            have hvalid : ValidMatrix r.dimension bs := by simpa [hbs] using hc.2.2.2
            have htag : (if decide (ValidMatrix r.dimension bs) then BSym.one else .zero) = BSym.one := by
              simp [hvalid]
            rw [htag, hc.2.1, hbs]
            rfl
          · intro hnon
            have hbad : ¬ ValidMatrix r.dimension bs := by
              intro hvalid
              exact hnon (canonical_packet_accept input bs hf hp0 hvalid)
            simp [frontendStore, hbad]
        · have hguard : frontendPacketGuard (fun k =>
              (frontendStore input r.dimension tail ((bs.map boolSym).reverse) [.one] [] [] k).head?) = false := by
              cases tail with
              | nil => exact (ht rfl).elim
              | cons a tail => rfl
          have hreject := frontendReject_exec
            (frontendStore input r.dimension tail ((bs.map boolSym).reverse) [.one] [] [])
            (by simp [frontendStore])
          have hinner := StackProg.Exec.branchFalse (test := frontendPacketGuard) (p := pm)
            hguard hreject
          have houter := StackProg.Exec.branchTrue (test := frontendHeaderGuard)
            (q := frontendReject) (by rw [frontendHeaderGuard_store, hf])
            (StackProg.Exec.seq hclear (StackProg.Exec.seq hpacket hinner))
          have hex := StackProg.Exec.seq hhead houter
          refine ⟨_, _, hex, ?_, ?_, ?_⟩
          · have hbudget := frontend_budget Ch input.length h (3*r.fuel+1) u 0 hh
              (by omega) hu' (by omega)
            omega
          · intro vertex G hinput
            have hc := canonical_front_packet G input hinput
            have hpEq : (bs, tail) = (graphBits G, []) := Option.some.inj (hp0.symm.trans hc.2.2.1)
            exact (ht (congrArg Prod.snd hpEq)).elim
          · intro _
            simp [frontendStore]
  · have hf' : r.found = false := Bool.eq_false_of_not_eq_true hf
    have hreject := frontendReject_exec (frontendHeaderStore input r) (by
      simp [frontendHeaderStore, frontendStore, hf'])
    have houter := StackProg.Exec.branchFalse (test := frontendHeaderGuard)
      (p := .seq (clearProg 6) (.seq pp (.branch frontendPacketGuard pm frontendReject)))
      (by rw [frontendHeaderGuard_store, hf']) hreject
    have hex := StackProg.Exec.seq hhead houter
    refine ⟨_, _, hex, ?_, ?_, ?_⟩
    · have hbudget := frontend_budget Ch input.length h 0 0 0 hh (by omega) (by omega) (by omega)
      omega
    · intro vertex G hinput
      have hc := canonical_front_packet G input hinput
      exact (hf hc.1).elim
    · intro _
      simp [frontendHeaderStore, frontendStore]

end TensorNP.Encoder
end


/- Inlined module: EncoderSource -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen
namespace TensorNP.Encoder

def encoderKeep : StackProg (Fin 32) BSym := .act (fun _ _ => .keep)

lemma encoderKeep_exec (s : Fin 32 → List BSym) : encoderKeep.Exec s s 1 := by
  have he : StackProg.applyAct (fun _ _ => StackAct.keep) s=s := by funext k; rfl
  simpa only [encoderKeep, he] using StackProg.Exec.act (fun _ _ => StackAct.keep) s

lemma encoderSource_budget (Cf Cb d L front back : ℕ)
    (hf : front≤Cf*(L+2)^5) (hb : back≤Cb*(L+2)^d) :
    front+back+3≤(Cf+Cb+3)*(L+2)^(d+5) := by
  have hp5 : (L+2)^5≤(L+2)^(d+5) := pow_le_pow_right₀ (by omega) (by omega)
  have hpd : (L+2)^d≤(L+2)^(d+5) := pow_le_pow_right₀ (by omega) (by omega)
  have hp0 : 1≤(L+2)^(d+5) := Nat.one_le_pow _ _ (by omega)
  have hf' := hf.trans (Nat.mul_le_mul_left Cf hp5)
  have hb' := hb.trans (Nat.mul_le_mul_left Cb hpd)
  rw [Nat.add_mul, Nat.add_mul]
  omega

/-- The frontend rejects every malformed input and exposes the unique canonical matrix otherwise. -/
theorem encoder_source_of_backend (backend : StackProg (Fin 32) BSym) (Cb d : ℕ)
    (hbackend : ∀ (input : List BSym) (v : ℕ) (G : SimpleGraph (Fin v)),
      ∃ (s : Fin 32 → List BSym) (steps : ℕ),
        backend.Exec (frontendGraphStore input v (graphData G)) s steps ∧
        steps≤Cb*(v+1)^d ∧ s 5=tensorCode (colorTensor G)) :
    ∃ (p : StackProg (Fin 32) BSym) (C : ℕ), ∀ input : List BSym,
      ∃ (s : Fin 32 → List BSym) (steps : ℕ), p.Exec (frontendInputStore input) s steps ∧
        steps≤C*(input.length+2)^(d+5) ∧ s 5=eigenEncoderValue input := by
  obtain ⟨front, Cf, hfront⟩ := graph_frontend_source
  refine ⟨.seq front (.branch frontendHeaderGuard backend encoderKeep), Cf+Cb+3, ?_⟩
  intro input
  obtain ⟨s, n, he, hn, hcorrect⟩ := hfront input
  classical
  by_cases hcan : ∃ (v : ℕ) (G : SimpleGraph (Fin v)), input=graphCode G
  · obtain ⟨v, G, hinput⟩ := hcan
    have hs : s=frontendGraphStore input v (graphData G) := by
      simpa only [graphData] using hcorrect.1 v G hinput
    rw [hs] at he
    obtain ⟨out, m, hb, hm, hout⟩ := hbackend input v G
    have hg : frontendHeaderGuard (fun k => (frontendGraphStore input v (graphData G) k).head?)=true := by
      simp [frontendHeaderGuard, frontendGraphStore, frontendStore]
    have hex := StackProg.Exec.seq he
      (StackProg.Exec.branchTrue (test := frontendHeaderGuard) (q := encoderKeep) hg hb)
    refine ⟨out, n+1+(1+m), hex, ?_, ?_⟩
    · have hv : v ≤ input.length := by simpa only [hinput] using graphCode_dimension_le G
      have hm' := hm.trans (Nat.mul_le_mul_left Cb
        (Nat.pow_le_pow_left (by omega : v+1 ≤ input.length+2) d))
      have hbudget := encoderSource_budget Cf Cb d input.length n m hn hm'
      omega
    · rw [hout, hinput, eigenEncoderValue_graphCode]
  · have hc := hcorrect.2 hcan
    have hg : frontendHeaderGuard (fun k => (s k).head?)=false := by
      simp [frontendHeaderGuard, hc.1]
    have hex := StackProg.Exec.seq he
      (StackProg.Exec.branchFalse (test := frontendHeaderGuard) (p := backend) hg (encoderKeep_exec s))
    refine ⟨s, n+1+(1+1), hex, ?_, ?_⟩
    · simpa using encoderSource_budget Cf Cb d input.length n 0 hn (by omega)
    · rw [hc.2, eigenEncoderValue_invalid input hcan]

end TensorNP.Encoder
end


/- Inlined module: NativeBridge -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen
namespace TensorNP.Encoder

/-- Every explicit source polynomial fits the exact Cook budget, including inputs of length zero. -/
theorem source_budget (A d : ℕ) : ∃ k, ∀ n : ℕ, A*(n+2)^d≤n^k+k := by
  let k := A+2*d+A*3^d+1
  refine ⟨k, ?_⟩
  intro n
  have hk : k≠0 := by dsimp [k]; omega
  by_cases hz : n=0
  · subst n
    have hb : A*2^d≤A*3^d := Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by decide) d)
    simp only [Nat.zero_add, zero_pow hk]
    dsimp [k]
    omega
  by_cases ho : n=1
  · subst n
    simp only [one_pow]
    dsimp [k]
    omega
  have hn : 2≤n := by omega
  have hc : A≤n^A :=
    (Nat.le_of_lt (Nat.lt_two_pow_self (n := A))).trans (Nat.pow_le_pow_left hn A)
  have hb : n+2≤n^2 := by nlinarith
  calc
    A*(n+2)^d ≤ n^A*(n^2)^d := Nat.mul_le_mul hc (Nat.pow_le_pow_left hb d)
    _ = n^(A+2*d) := by rw [pow_add, pow_mul]
    _ ≤ n^k+k := by
      have hp : n^(A+2*d)≤n^k := Nat.pow_le_pow_right (by omega) (by dsimp [k]; omega)
      omega

theorem encoder_polytime_of_backend (backend : StackProg (Fin 32) BSym) (Cb d : ℕ)
    (hbackend : ∀ (input : List BSym) (v : ℕ) (G : SimpleGraph (Fin v)),
      ∃ (s : Fin 32 → List BSym) (steps : ℕ),
        backend.Exec (frontendGraphStore input v (graphData G)) s steps ∧
        steps≤Cb*(v+1)^d ∧ s 5=tensorCode (colorTensor G)) :
    CookPvsNP.PolyTimeComputable eigenEncoderValue := by
  obtain ⟨p, C, hp⟩ := encoder_source_of_backend backend Cb d hbackend
  obtain ⟨k, hk⟩ := source_budget C (d+5)
  apply CookPvsNP.stack_program_polytime p (0 : Fin 32) 5 eigenEncoderValue k
  intro input
  obtain ⟨s, n, he, hn, hout⟩ := hp input
  exact ⟨s, n, hn.trans (hk input.length), he, hout⟩

end TensorNP.Encoder
end


/- Inlined module: GraphPayload -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen TensorNP.Encoder
namespace TensorNP.BilinearEncoder

/-- Apply a payload to the canonical adjacency packet, rejecting every non-code. -/
def graphEncoderValue (payload : ℕ → List BSym → List BSym) (input : List BSym) : List BSym :=
  let r := boundedHeader 0 (input.length+1) input
  if graphInputValid input then
    match parseBits (r.dimension*r.dimension) r.suffix with
    | none => []
    | some (bs, _) => payload r.dimension (bs.map boolSym)
  else []

theorem graphEncoderValue_graphCode (payload : ℕ → List BSym → List BSym)
    {v : ℕ} (G : SimpleGraph (Fin v)) :
    graphEncoderValue payload (graphCode G) = payload v (graphData G) := by
  have hc := canonical_front_packet G (graphCode G) rfl
  simp only [graphEncoderValue, graphInputValid_graphCode, ↓reduceIte]
  rw [hc.2.2.1, hc.2.1]
  rfl

theorem graphEncoderValue_invalid (payload : ℕ → List BSym → List BSym) (input : List BSym)
    (h : ¬ ∃ (v : ℕ) (G : SimpleGraph (Fin v)), input = graphCode G) :
    graphEncoderValue payload input = [] := by
  simp [graphEncoderValue, graphInputValid_invalid input h]

theorem graph_encoder_source_of_backend (payload : ℕ → List BSym → List BSym)
    (backend : StackProg (Fin 32) BSym) (Cb d : ℕ)
    (hbackend : ∀ (input : List BSym) (v : ℕ) (G : SimpleGraph (Fin v)),
      ∃ (s : Fin 32 → List BSym) (steps : ℕ),
        backend.Exec (frontendGraphStore input v (graphData G)) s steps ∧
        steps ≤ Cb*(v+1)^d ∧ s 5 = payload v (graphData G)) :
    ∃ (p : StackProg (Fin 32) BSym) (C : ℕ), ∀ input : List BSym,
      ∃ (s : Fin 32 → List BSym) (steps : ℕ), p.Exec (frontendInputStore input) s steps ∧
        steps ≤ C*(input.length+2)^(d+5) ∧ s 5 = graphEncoderValue payload input := by
  obtain ⟨front, Cf, hfront⟩ := graph_frontend_source
  refine ⟨.seq front (.branch frontendHeaderGuard backend encoderKeep), Cf+Cb+3, ?_⟩
  intro input
  obtain ⟨s, n, he, hn, hcorrect⟩ := hfront input
  classical
  by_cases hcan : ∃ (v : ℕ) (G : SimpleGraph (Fin v)), input = graphCode G
  · obtain ⟨v, G, hinput⟩ := hcan
    have hs : s = frontendGraphStore input v (graphData G) := by
      simpa only [graphData] using hcorrect.1 v G hinput
    rw [hs] at he
    obtain ⟨out, m, hb, hm, hout⟩ := hbackend input v G
    have hg : frontendHeaderGuard (fun k => (frontendGraphStore input v (graphData G) k).head?) = true := by
      simp [frontendHeaderGuard, frontendGraphStore, frontendStore]
    have hex := StackProg.Exec.seq he
      (StackProg.Exec.branchTrue (test := frontendHeaderGuard) (q := encoderKeep) hg hb)
    refine ⟨out, n+1+(1+m), hex, ?_, ?_⟩
    · have hv : v ≤ input.length := by simpa only [hinput] using graphCode_dimension_le G
      have hm' := hm.trans (Nat.mul_le_mul_left Cb
        (Nat.pow_le_pow_left (by omega : v+1 ≤ input.length+2) d))
      have hbudget := encoderSource_budget Cf Cb d input.length n m hn hm'
      omega
    · rw [hout, hinput, graphEncoderValue_graphCode]
  · have hc := hcorrect.2 hcan
    have hg : frontendHeaderGuard (fun k => (s k).head?) = false := by
      simp [frontendHeaderGuard, hc.1]
    have hex := StackProg.Exec.seq he
      (StackProg.Exec.branchFalse (test := frontendHeaderGuard) (p := backend) hg (encoderKeep_exec s))
    refine ⟨s, n+1+(1+1), hex, ?_, ?_⟩
    · simpa using encoderSource_budget Cf Cb d input.length n 0 hn (by omega)
    · rw [hc.2, graphEncoderValue_invalid payload input hcan]

theorem graph_encoder_polytime_of_backend (payload : ℕ → List BSym → List BSym)
    (backend : StackProg (Fin 32) BSym) (Cb d : ℕ)
    (hbackend : ∀ (input : List BSym) (v : ℕ) (G : SimpleGraph (Fin v)),
      ∃ (s : Fin 32 → List BSym) (steps : ℕ),
        backend.Exec (frontendGraphStore input v (graphData G)) s steps ∧
        steps ≤ Cb*(v+1)^d ∧ s 5 = payload v (graphData G)) :
    CookPvsNP.PolyTimeComputable (graphEncoderValue payload) := by
  obtain ⟨p, C, hp⟩ := graph_encoder_source_of_backend payload backend Cb d hbackend
  obtain ⟨k, hk⟩ := source_budget C (d+5)
  apply CookPvsNP.stack_program_polytime p (0 : Fin 32) 5 (graphEncoderValue payload) k
  intro input
  obtain ⟨s, n, he, hn, hout⟩ := hp input
  exact ⟨s, n, hn.trans (hk input.length), he, hout⟩

end TensorNP.BilinearEncoder
end


/- Inlined module: CastBridge -/
section
set_option autoImplicit false
namespace TensorNP.BilinearEncoder

/-- Normalize integer coefficients through the published rational code. -/
lemma complex_int_rat_cast (z : ℤ) : ((z : ℚ) : ℂ) = (z : ℂ) := by
  apply Complex.ext <;> simp

end TensorNP.BilinearEncoder
end


/- Inlined module: TotalTensors -/
section
set_option autoImplicit false
open TensorNP.Bilinear
namespace TensorNP.BilinearEncoder

def complexSlices : ℕ → ℕ
  | 0 => 1
  | v + 1 => (v+1) * (2*(v+1)+5)

noncomputable def complexTensor : {v : ℕ} → SimpleGraph (Fin v) →
    Fin (complexSlices v) → Fin (2*v+1) → Fin (2*v+1) → ℚ
  | 0, _ => fun _ _ _ => 0
  | v+1, G => fun s p q => (AG G (explicitSliceEquiv (v+1) s) p q : ℚ)

noncomputable def realTensor {v : ℕ} (G : SimpleGraph (Fin v)) :
    Fin (complexSlices v + complexSlices v) →
    Fin ((2*v+1)+(2*v+1)) → Fin ((2*v+1)+(2*v+1)) → ℚ :=
  fun s p q => doubling (complexTensor G) (finSumFinEquiv.symm s)
    (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)

theorem complexTensor_correct {v : ℕ} (G : SimpleGraph (Fin v)) :
    TBF (fun s p q => (complexTensor G s p q : ℂ)) ↔ G.Colorable 3 := by
  cases v with
  | zero =>
      constructor
      · intro _
        exact SimpleGraph.Colorable.of_isEmpty 3
      · intro _
        refine ⟨1, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro h
          have h' := congrFun h (0 : Fin 1)
          change (1 : ℂ) = 0 at h'
          exact one_ne_zero h'
        · intro h
          have h' := congrFun h (0 : Fin 1)
          change (1 : ℂ) = 0 at h'
          exact one_ne_zero h'
        · intro h
          have h' := congrFun h (0 : Fin 1)
          change (1 : ℂ) = 0 at h'
          exact one_ne_zero h'
        · intro s
          simp [complexTensor]
        · intro p
          simp [complexTensor]
        · intro q
          simp [complexTensor]
  | succ v =>
      have h := tbf_reindex_iff (explicitSliceEquiv (v+1))
        (Equiv.refl (Fin (2*(v+1)+1))) (Equiv.refl (Fin (2*(v+1)+1)))
        (fun s p q => (AG G s p q : ℂ))
      have hc := h.symm.trans (AG_feasible_iff_colorable G (by omega))
      have hcoeff : (fun s : Fin (complexSlices (v+1)) => fun p q => (complexTensor G s p q : ℂ)) =
          (fun s : Fin (complexSlices (v+1)) => fun p q => (AG G (explicitSliceEquiv (v+1) s) p q : ℂ)) := by
        funext s p q
        change ((AG G (explicitSliceEquiv (v+1) s) p q : ℚ) : ℂ) = (AG G (explicitSliceEquiv (v+1) s) p q : ℂ)
        exact complex_int_rat_cast _
      rw [hcoeff]
      exact hc

private lemma doubling_cast_real {I J K : Type} (A : I → J → K → ℚ)
    (i : I ⊕ I) (j : J ⊕ J) (k : K ⊕ K) :
    ((doubling A i j k : ℚ) : ℝ) = doubling (fun i j k => (A i j k : ℝ)) i j k := by
  cases i <;> cases j <;> cases k <;> simp [doubling]

theorem realTensor_correct {v : ℕ} (G : SimpleGraph (Fin v)) :
    TBF (fun s p q => (realTensor G s p q : ℝ)) ↔ G.Colorable 3 := by
  have h := tbf_reindex_iff
    (finSumFinEquiv.symm : Fin (complexSlices v + complexSlices v) ≃
      Fin (complexSlices v) ⊕ Fin (complexSlices v))
    (finSumFinEquiv.symm : Fin ((2*v+1)+(2*v+1)) ≃ Fin (2*v+1) ⊕ Fin (2*v+1))
    (finSumFinEquiv.symm : Fin ((2*v+1)+(2*v+1)) ≃ Fin (2*v+1) ⊕ Fin (2*v+1))
    (doubling (fun s p q => (complexTensor G s p q : ℝ)))
  have hc : TBF (fun s p q => (realTensor G s p q : ℝ)) ↔
      TBF (doubling (fun s p q => (complexTensor G s p q : ℝ))) := by
    simpa only [realTensor, doubling_cast_real] using h.symm
  rw [TensorNP.Bilinear.lemma_3_6] at hc
  simpa only [Complex.ofReal_ratCast] using hc.trans (complexTensor_correct G)

end TensorNP.BilinearEncoder
end


/- Inlined module: Reduction -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Bilinear TensorNP.Encoder
namespace TensorNP.BilinearEncoder

theorem tensorCode_mem_iff (F : Type*) [Field F] {l m n : ℕ}
    (A : Fin l → Fin m → Fin n → ℚ) :
    TensorNP.Bilinear.tensorCode A ∈ TensorNP.Bilinear.tbfLang F ↔
      TensorNP.Bilinear.TBF (fun i j k => (A i j k : F)) := by
  constructor
  · rintro ⟨l', m', n', B, hB, hcode⟩
    obtain ⟨hl, hm, hn, hAB⟩ := TensorNP.BilinearCode.tensorCode_unique A B hcode
    subst l'
    subst m'
    subst n'
    have heq : A = B := eq_of_heq hAB
    subst B
    exact hB
  · intro h
    exact ⟨l, m, n, A, h, rfl⟩

theorem graph_payload_reduction (F : Type*) [Field F]
    (payload : ℕ → List BSym → List BSym)
    (hpoly : PolyTimeComputable (graphEncoderValue payload))
    (hsem : ∀ (v : ℕ) (G : SimpleGraph (Fin v)),
      payload v (graphData G) ∈ TensorNP.Bilinear.tbfLang F ↔ G.Colorable 3) :
    PolyReducible TensorNP.Eigen.threeColLang (TensorNP.Bilinear.tbfLang F) := by
  refine ⟨graphEncoderValue payload, hpoly, ?_⟩
  intro w
  constructor
  · rintro ⟨v, G, hcolor, rfl⟩
    rw [graphEncoderValue_graphCode]
    exact (hsem v G).2 hcolor
  · intro hout
    by_cases hc : ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = TensorNP.Eigen.graphCode G
    · obtain ⟨v, G, hw⟩ := hc
      refine ⟨v, G, ?_, hw⟩
      rw [hw, graphEncoderValue_graphCode] at hout
      exact (hsem v G).1 hout
    · rw [graphEncoderValue_invalid payload w hc] at hout
      exact False.elim (TensorNP.BilinearCode.empty_not_tbfLang F hout)

theorem complexTensor_code_mem_iff {v : ℕ} (G : SimpleGraph (Fin v)) :
    TensorNP.Bilinear.tensorCode (complexTensor G) ∈ TensorNP.Bilinear.tbfLang ℂ ↔ G.Colorable 3 :=
  (tensorCode_mem_iff ℂ (complexTensor G)).trans (complexTensor_correct G)

theorem realTensor_code_mem_iff {v : ℕ} (G : SimpleGraph (Fin v)) :
    TensorNP.Bilinear.tensorCode (realTensor G) ∈ TensorNP.Bilinear.tbfLang ℝ ↔ G.Colorable 3 :=
  (tensorCode_mem_iff ℝ (realTensor G)).trans (realTensor_correct G)

end TensorNP.BilinearEncoder
end


/- Inlined module: UnaryCompare -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def compareStore (x y left right : ℕ) (flags : List BSym) : Fin 6 → List BSym :=
  fun k => if k = 0 then List.replicate x .one else if k = 1 then List.replicate y .one
    else if k = 2 then List.replicate left .one else if k = 3 then List.replicate right .one
    else if k = 5 then flags else []

private def cancelGuard (h : Fin 6 → Option BSym) : Bool := (h 2).isSome && (h 3).isSome
private def cancelAct (_ : Fin 6 → Option BSym) (k : Fin 6) : StackAct BSym :=
  if k = 2 ∨ k = 3 then .pop else .keep
private def cancelLoop : StackProg (Fin 6) BSym := .loop cancelGuard (.act cancelAct)

private lemma cancel_step (x y left right : ℕ) (flags : List BSym) :
    StackProg.applyAct cancelAct (compareStore x y (left + 1) (right + 1) flags) =
      compareStore x y left right flags := by
  funext k
  fin_cases k <;> rfl

private lemma cancel_exec (x y left right : ℕ) (flags : List BSym) :
    cancelLoop.Exec (compareStore x y left right flags)
      (compareStore x y (left - right) (right - left) flags) (3 * min left right + 1) := by
  induction left generalizing right with
  | zero =>
      simpa [cancelLoop, cancelGuard, compareStore] using
        (StackProg.Exec.loopFalse (p := .act cancelAct)
          (s := compareStore x y 0 right flags) (by simp [cancelGuard, compareStore]))
  | succ left ih =>
      cases right with
      | zero =>
          simpa [cancelLoop, cancelGuard, compareStore] using
            (StackProg.Exec.loopFalse (p := .act cancelAct)
              (s := compareStore x y (left + 1) 0 flags) (by simp [cancelGuard, compareStore]))
      | succ right =>
          have hg : cancelGuard (fun k => (compareStore x y (left + 1) (right + 1) flags k).head?) = true := by rfl
          have ha : (StackProg.act cancelAct).Exec (compareStore x y (left + 1) (right + 1) flags)
              (compareStore x y left right flags) 1 := by
            simpa only [cancel_step] using (StackProg.Exec.act cancelAct
              (compareStore x y (left + 1) (right + 1) flags))
          have he := StackProg.Exec.loopTrue hg ha (ih right)
          simpa [cancelLoop, Nat.succ_sub_succ_eq_sub, Nat.succ_min_succ, Nat.mul_add,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

private def ltFlag (left right : ℕ) : BSym :=
  if left = 0 ∧ 0 < right then .one else .zero

private def eqFlag (left right : ℕ) : BSym :=
  if left = 0 ∧ right = 0 then .one else .zero

private def ltAct (h : Fin 6 → Option BSym) (k : Fin 6) : StackAct BSym :=
  if k = 5 then .push (if (h 2).isNone && (h 3).isSome then .one else .zero) else .keep

private def eqAct (h : Fin 6 → Option BSym) (k : Fin 6) : StackAct BSym :=
  if k = 5 then .push (if (h 2).isNone && (h 3).isNone then .one else .zero) else .keep

private lemma lt_step (x y left right : ℕ) (flags : List BSym) :
    StackProg.applyAct ltAct (compareStore x y left right flags) =
      compareStore x y left right (ltFlag left right :: flags) := by
  cases left <;> cases right <;> funext k <;> fin_cases k <;> rfl

private lemma eq_step (x y left right : ℕ) (flags : List BSym) :
    StackProg.applyAct eqAct (compareStore x y left right flags) =
      compareStore x y left right (eqFlag left right :: flags) := by
  cases left <;> cases right <;> funext k <;> fin_cases k <;> rfl

private def compareProgram : StackProg (Fin 6) BSym :=
  .seq (copyProg 0 2 4) (.seq (copyProg 1 3 4)
    (.seq cancelLoop (.seq (.act ltAct) (.act eqAct))))

theorem unary_compare_machine : ∃ p : StackProg (Fin 6) BSym, ∀ x y : ℕ, ∃ steps,
    p.Exec (compareStore x y 0 0 [])
      (compareStore x y (x-y) (y-x)
        [if x=y then BSym.one else .zero, if x<y then BSym.one else .zero]) steps ∧
    steps ≤ 10 * (x + y + 2) := by
  refine ⟨compareProgram, ?_⟩
  intro x y
  have he1 : (copyProg 0 2 4).Exec (compareStore x y 0 0 [])
      (compareStore x y x 0 []) (6 * x + 3) := by
    have he := stack_copy (0 : Fin 6) 2 4 (by decide) (by decide) (by decide)
      (compareStore x y 0 0 []) (by rfl)
    have heq : Function.update (compareStore x y 0 0 []) 2
        ((compareStore x y 0 0 []) 0 ++ (compareStore x y 0 0 []) 2) =
        compareStore x y x 0 [] := by
      funext k
      fin_cases k <;> simp [compareStore, Function.update]
    rw [heq] at he
    simpa [compareStore] using he
  have he2 : (copyProg 1 3 4).Exec (compareStore x y x 0 [])
      (compareStore x y x y []) (6 * y + 3) := by
    have he := stack_copy (1 : Fin 6) 3 4 (by decide) (by decide) (by decide)
      (compareStore x y x 0 []) (by rfl)
    have heq : Function.update (compareStore x y x 0 []) 3
        ((compareStore x y x 0 []) 1 ++ (compareStore x y x 0 []) 3) =
        compareStore x y x y [] := by
      funext k
      fin_cases k <;> simp [compareStore, Function.update]
    rw [heq] at he
    simpa [compareStore] using he
  have he3 := cancel_exec x y x y []
  have he4 : (StackProg.act ltAct).Exec (compareStore x y (x-y) (y-x) [])
      (compareStore x y (x-y) (y-x) [ltFlag (x-y) (y-x)]) 1 := by
    simpa only [lt_step] using (StackProg.Exec.act ltAct (compareStore x y (x-y) (y-x) []))
  have he5 : (StackProg.act eqAct).Exec
      (compareStore x y (x-y) (y-x) [ltFlag (x-y) (y-x)])
      (compareStore x y (x-y) (y-x) [eqFlag (x-y) (y-x), ltFlag (x-y) (y-x)]) 1 := by
    simpa only [eq_step] using (StackProg.Exec.act eqAct
      (compareStore x y (x-y) (y-x) [ltFlag (x-y) (y-x)]))
  have hflags : [eqFlag (x-y) (y-x), ltFlag (x-y) (y-x)] =
      [if x = y then BSym.one else .zero, if x < y then BSym.one else .zero] := by
    have heq : (x-y = 0 ∧ y-x = 0) ↔ x = y := by omega
    have hlt : (x-y = 0 ∧ 0 < y-x) ↔ x < y := by omega
    simp only [eqFlag, ltFlag, heq, hlt]
  have he := StackProg.Exec.seq he1 (StackProg.Exec.seq he2
    (StackProg.Exec.seq he3 (StackProg.Exec.seq he4 he5)))
  refine ⟨6*x + 3 + 1 + (6*y + 3 + 1 + (3*min x y + 1 + 1 + (1 + 1 + 1))), ?_, ?_⟩
  · simpa only [compareProgram, hflags] using he
  · have hmin := Nat.min_le_left x y
    omega

end TensorNP.Encoder
end


/- Inlined module: RegisterCompare -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

lemma register_write_at {M : ℕ} {A : Type} (r : Fin 6 ↪ Fin M)
    (t : Fin 6 → List A) (frame : Fin M → List A) (k : Fin 6) :
    StackProgPortLift.write r t frame (r k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := r.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma register_write_outside {M : ℕ} {A : Type} (r : Fin 6 ↪ Fin M)
    (t : Fin 6 → List A) (frame : Fin M → List A) (l : Fin M)
    (h : ∀ k, r k ≠ l) : StackProgPortLift.write r t frame l = frame l := by
  classical
  have hex : ¬ ∃ k, r k = l := by
    rintro ⟨k, hk⟩
    exact h k hk
  simp [StackProgPortLift.write, hex]

lemma register_project_write {M : ℕ} {A : Type} (r : Fin 6 ↪ Fin M)
    (t : Fin 6 → List A) (frame : Fin M → List A) :
    StackProgPortLift.project r (StackProgPortLift.write r t frame) = t := by
  funext k
  exact register_write_at r t frame k

lemma register_write_overwrite {M : ℕ} {A : Type} (r : Fin 6 ↪ Fin M)
    (u t : Fin 6 → List A) (frame : Fin M → List A) :
    StackProgPortLift.write r u (StackProgPortLift.write r t frame) =
      StackProgPortLift.write r u frame := by
  funext l
  by_cases h : ∃ k, r k = l
  · obtain ⟨k, rfl⟩ := h
    rw [register_write_at, register_write_at]
  · have hout : ∀ k, r k ≠ l := by
      intro k hk
      exact h ⟨k, hk⟩
    rw [register_write_outside r u _ l hout, register_write_outside r t frame l hout,
      register_write_outside r u frame l hout]

noncomputable def registerDecode {M : ℕ} (r : Fin 6 ↪ Fin M) (l : Fin M) : Option (Fin 6) := by
  classical
  exact if h : ∃ k, r k = l then some (Classical.choose h) else none

lemma registerDecode_spec {M : ℕ} (r : Fin 6 ↪ Fin M) (l : Fin M) (k : Fin 6) :
    registerDecode r l = some k ↔ r k = l := by
  classical
  unfold registerDecode
  split
  · rename_i h
    constructor
    · intro hk
      have hchoose : Classical.choose h = k := Option.some.inj hk
      simpa only [hchoose] using Classical.choose_spec h
    · intro hk
      have hchoose : Classical.choose h = k := r.injective ((Classical.choose_spec h).trans hk.symm)
      simp only [hchoose]
  · rename_i h
    constructor
    · intro hk
      contradiction
    · intro hk
      exact False.elim (h ⟨k, hk⟩)

theorem unary_compare_framed (M : ℕ) (r : Fin 6 ↪ Fin M) :
    ∃ p : StackProg (Fin M) BSym, ∀ (x y : ℕ) (frame : Fin M → List BSym), ∃ steps,
      p.Exec (StackProgPortLift.write r (compareStore x y 0 0 []) frame)
        (StackProgPortLift.write r (compareStore x y (x - y) (y - x)
          [if x = y then BSym.one else .zero, if x < y then BSym.one else .zero]) frame) steps ∧
      steps ≤ 10 * (x + y + 2) := by
  obtain ⟨p, hp⟩ := unary_compare_machine
  refine ⟨StackProgPortLift.liftProgC r (registerDecode r) p, ?_⟩
  intro x y frame
  obtain ⟨steps, he, hb⟩ := hp x y
  refine ⟨steps, ?_, hb⟩
  have he' := StackProgPortLift.liftProgC_exec r (registerDecode r)
    (registerDecode_spec r) he (StackProgPortLift.write r (compareStore x y 0 0 []) frame)
    (register_project_write r (compareStore x y 0 0 []) frame)
  rw [register_write_overwrite] at he'
  exact he'

end TensorNP.Encoder
end


/- Inlined module: RegisterSpec -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

/-- Twenty-one unary registers, disjoint from immutable lists and seven work ports. -/
def regPorts : Fin 21 ↪ Fin 32 :=
  ⟨![1,2,3,6,8,9,10,11,12,13,14,15,16,17,23,24,27,28,29,30,31], by decide⟩

def regScratch (l : Fin 32) : Prop := l=18 ∨ l=19 ∨ l=20 ∨ l=21 ∨ l=22 ∨ l=25 ∨ l=26
instance (l : Fin 32) : Decidable (regScratch l) :=
  inferInstanceAs (Decidable (l = 18 ∨ l = 19 ∨ l = 20 ∨ l = 21 ∨ l = 22 ∨ l = 25 ∨ l = 26))

def regBase (frame : Fin 32 → List BSym) : Fin 32 → List BSym :=
  fun l => if regScratch l then [] else frame l

noncomputable def regStore (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) : Fin 32 → List BSym :=
  StackProgPortLift.write regPorts (fun r => List.replicate (R r) .one) (regBase frame)

lemma port_write_at {K L A : Type} (r : K ↪ L) (t : K → List A) (s : L → List A) (k : K) :
    StackProgPortLift.write r t s (r k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    rw [r.injective (Classical.choose_spec h)]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma port_write_outside {K L A : Type} (r : K ↪ L) (t : K → List A) (s : L → List A) (l : L)
    (h : ∀ k, r k ≠ l) : StackProgPortLift.write r t s l = s l := by
  classical
  have hn : ¬ ∃ k, r k = l := by rintro ⟨k, hk⟩; exact h k hk
  simp [StackProgPortLift.write, hn]

@[simp] lemma regStore_at (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) :
    regStore frame R (regPorts r) = List.replicate (R r) .one :=
  port_write_at regPorts _ _ r

lemma regPorts_not_scratch (r : Fin 21) : ¬ regScratch (regPorts r) := by
  fin_cases r <;> decide

lemma regScratch_outside (l : Fin 32) (h : regScratch l) (r : Fin 21) : regPorts r ≠ l := by
  intro he
  exact regPorts_not_scratch r (he.symm ▸ h)

lemma regStore_scratch (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (l : Fin 32)
    (h : regScratch l) : regStore frame R l = [] := by
  rw [regStore, port_write_outside _ _ _ _ (regScratch_outside l h)]
  simp [regBase, h]

lemma regStore_update (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) (n : ℕ) :
    regStore frame (Function.update R r n) =
      Function.update (regStore frame R) (regPorts r) (List.replicate n .one) := by
  classical
  funext l
  by_cases h : ∃ k, regPorts k = l
  · obtain ⟨k, rfl⟩ := h
    rw [regStore_at]
    by_cases hk : k = r
    · subst k
      simp
    · have hp : regPorts k ≠ regPorts r := fun he => hk (regPorts.injective he)
      simp [hk, hp]
  · have hout : ∀ k, regPorts k ≠ l := by rintro k hk; exact h ⟨k, hk⟩
    have hl : l ≠ regPorts r := fun he => h ⟨r, he.symm⟩
    simp only [regStore, port_write_outside _ _ _ _ hout]
    simp only [Function.update_of_ne hl]
    rw [port_write_outside _ _ _ _ hout]

def regSize (R : Fin 21 → ℕ) : ℕ := ∑ r, R r

lemma reg_le_size (R : Fin 21 → ℕ) (r : Fin 21) : R r ≤ regSize R := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)

end TensorNP.Encoder
end


/- Inlined module: CounterLanguage -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

abbrev RegFile := Fin 21 → ℕ

def regCharge (R : RegFile) : ℕ := 100*(regSize R+1)

def regCompare (less : Bool) (r s : Fin 21) (R : RegFile) : Bool :=
  if less then decide (R r < R s) else decide (R r = R s)

def regNeighbor (data : List BSym) (R : RegFile) : Bool :=
  decide (data.getD (R 3*R 0+R 8) .zero = .one)

/-- A finite counter language; the sole graph operation reads the immutable adjacency table. -/
inductive RegCmd where
  | skip
  | reset (r : Fin 21)
  | inc (r : Fin 21)
  | assign (dst src : Fin 21)
  | add (dst src : Fin 21) (h : dst ≠ src)
  | sub (dst src : Fin 21) (h : dst ≠ src)
  | seq (p q : RegCmd)
  | branch (less : Bool) (r s : Fin 21) (yes no : RegCmd)
  | neighbor (yes no : RegCmd)
  | down (r : Fin 21) (body : RegCmd)

/-- The cost bounds every source action, including unary work, guards and program transfers. -/
inductive RegExec (data : List BSym) : RegCmd → RegFile → RegFile → ℕ → Prop where
  | skip (R) : RegExec data .skip R R 1
  | reset (R r) : RegExec data (.reset r) R (Function.update R r 0) (regCharge R)
  | inc (R r) : RegExec data (.inc r) R (Function.update R r (R r+1)) (regCharge R)
  | assign (R dst src) : RegExec data (.assign dst src) R (Function.update R dst (R src)) (regCharge R)
  | add (R dst src h) : RegExec data (.add dst src h) R
      (Function.update R dst (R src+R dst)) (regCharge R)
  | sub (R dst src h) : RegExec data (.sub dst src h) R
      (Function.update R dst (R dst-R src)) (regCharge R)
  | seq {p q R T U n m} : RegExec data p R T n → RegExec data q T U m →
      RegExec data (.seq p q) R U (n+1+m)
  | branch {less r s yes no R T n} :
      RegExec data (if regCompare less r s R then yes else no) R T n →
      RegExec data (.branch less r s yes no) R T (regCharge R+n)
  | neighbor {yes no R T n} : R 3 < R 0 → R 8 < R 0 → data.length = R 0*R 0 →
      RegExec data (if regNeighbor data R then yes else no) R T n →
      RegExec data (.neighbor yes no) R T (100*(R 0+1)^2+n)
  | downFalse {r body R} : R r = 0 → RegExec data (.down r body) R R 1
  | downTrue {r body R T U n m} : 0 < R r →
      RegExec data body (Function.update R r (R r-1)) T n →
      RegExec data (.down r body) T U m →
      RegExec data (.down r body) R U (n+m+5)

/-- Each field is an independently checkable implementation of one counter instruction. -/
structure RegBackend where
  keep : StackProg (Fin 32) BSym
  reset : Fin 21 → StackProg (Fin 32) BSym
  inc : Fin 21 → StackProg (Fin 32) BSym
  assign : Fin 21 → Fin 21 → StackProg (Fin 32) BSym
  add : (dst src : Fin 21) → dst ≠ src → StackProg (Fin 32) BSym
  sub : (dst src : Fin 21) → dst ≠ src → StackProg (Fin 32) BSym
  branch : Bool → Fin 21 → Fin 21 → StackProg (Fin 32) BSym → StackProg (Fin 32) BSym → StackProg (Fin 32) BSym
  neighbor : StackProg (Fin 32) BSym → StackProg (Fin 32) BSym → StackProg (Fin 32) BSym
  keep_ok : ∀ frame R, keep.Exec (regStore frame R) (regStore frame R) 1
  reset_ok : ∀ frame R r, ∃ n, (reset r).Exec (regStore frame R)
    (regStore frame (Function.update R r 0)) n ∧ n ≤ regCharge R
  inc_ok : ∀ frame R r, ∃ n, (inc r).Exec (regStore frame R)
    (regStore frame (Function.update R r (R r+1))) n ∧ n ≤ regCharge R
  assign_ok : ∀ frame R dst src, ∃ n, (assign dst src).Exec (regStore frame R)
    (regStore frame (Function.update R dst (R src))) n ∧ n ≤ regCharge R
  add_ok : ∀ frame R dst src h, ∃ n, (add dst src h).Exec (regStore frame R)
    (regStore frame (Function.update R dst (R src+R dst))) n ∧ n ≤ regCharge R
  sub_ok : ∀ frame R dst src h, ∃ n, (sub dst src h).Exec (regStore frame R)
    (regStore frame (Function.update R dst (R dst-R src))) n ∧ n ≤ regCharge R
  pop_ok : ∀ frame R r, (popProg (regPorts r)).Exec (regStore frame R)
    (regStore frame (Function.update R r (R r-1))) 1
  branch_ok : ∀ less r s yes no frame R T n,
    (if regCompare less r s R then yes else no).Exec (regStore frame R) T n →
    ∃ m, (branch less r s yes no).Exec (regStore frame R) T m ∧ m ≤ regCharge R+n
  neighbor_ok : ∀ yes no frame R T n, R 3<R 0 → R 8<R 0 → (frame 7).length=R 0*R 0 →
    (if regNeighbor (frame 7) R then yes else no).Exec (regStore frame R) T n →
    ∃ m, (neighbor yes no).Exec (regStore frame R) T m ∧ m ≤ 100*(R 0+1)^2+n

noncomputable def compileReg (B : RegBackend) : RegCmd → StackProg (Fin 32) BSym
  | .skip => B.keep
  | .reset r => B.reset r
  | .inc r => B.inc r
  | .assign dst src => B.assign dst src
  | .add dst src h => B.add dst src h
  | .sub dst src h => B.sub dst src h
  | .seq p q => .seq (compileReg B p) (compileReg B q)
  | .branch less r s yes no => B.branch less r s (compileReg B yes) (compileReg B no)
  | .neighbor yes no => B.neighbor (compileReg B yes) (compileReg B no)
  | .down r body => .loop (fun h => (h (regPorts r)).isSome)
      (.seq (popProg (regPorts r)) (compileReg B body))

private theorem regStore_guard (frame : Fin 32 → List BSym) (R : RegFile) (r : Fin 21) :
    ((regStore frame R (regPorts r)).head?).isSome = decide (0<R r) := by
  rw [regStore_at]
  cases h : R r <;> simp [List.replicate_succ]

theorem compileReg_sound (B : RegBackend) {data : List BSym} {p : RegCmd} {R T : RegFile} {n : ℕ}
    (h : RegExec data p R T n) (frame : Fin 32 → List BSym) (hdata : frame 7 = data) :
    ∃ m, (compileReg B p).Exec (regStore frame R) (regStore frame T) m ∧ m ≤ n := by
  induction h with
  | skip R => exact ⟨1, B.keep_ok frame R, le_rfl⟩
  | reset R r => exact B.reset_ok frame R r
  | inc R r => exact B.inc_ok frame R r
  | assign R dst src => exact B.assign_ok frame R dst src
  | add R dst src h => exact B.add_ok frame R dst src h
  | sub R dst src h => exact B.sub_ok frame R dst src h
  | seq hp hq ihp ihq =>
      obtain ⟨u, hu, hub⟩ := ihp
      obtain ⟨v, hv, hvb⟩ := ihq
      exact ⟨u+1+v, StackProg.Exec.seq hu hv, by omega⟩
  | @branch less r s yes no R T n hp ih =>
      obtain ⟨u, hu, hub⟩ := ih
      have hu' : (if regCompare less r s R then compileReg B yes else compileReg B no).Exec
          (regStore frame R) (regStore frame T) u := by
        split <;> simp_all
      obtain ⟨v, hv, hvb⟩ := B.branch_ok less r s _ _ frame R _ u hu'
      exact ⟨v, hv, by omega⟩
  | @neighbor yes no R T n hr hc hlen hp ih =>
      obtain ⟨u, hu, hub⟩ := ih
      have hu' : (if regNeighbor (frame 7) R then compileReg B yes else compileReg B no).Exec
          (regStore frame R) (regStore frame T) u := by
        rw [hdata]
        split <;> simp_all
      obtain ⟨v, hv, hvb⟩ := B.neighbor_ok _ _ frame R _ u hr hc (by simpa [hdata] using hlen) hu'
      exact ⟨v, hv, by omega⟩
  | @downFalse r body R hz =>
      refine ⟨1, ?_, le_rfl⟩
      apply StackProg.Exec.loopFalse
      rw [regStore_guard]
      simp [hz]
  | @downTrue r body R T U n m hpos hp hl ihp ihl =>
      obtain ⟨u, hu, hub⟩ := ihp
      obtain ⟨v, hv, hvb⟩ := ihl
      have hg : ((regStore frame R (regPorts r)).head?).isSome = true := by
        rw [regStore_guard]
        exact decide_eq_true hpos
      refine ⟨1+(1+1+u)+1+v, ?_, by omega⟩
      exact StackProg.Exec.loopTrue hg (StackProg.Exec.seq (B.pop_ok frame R r) hu) hv

end TensorNP.Encoder
end


/- Inlined module: RegisterMacros -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def regKeep : StackProg (Fin 32) BSym := .act (fun _ _ => .keep)
def regReset (r : Fin 21) : StackProg (Fin 32) BSym := clearProg (regPorts r)
def regInc (r : Fin 21) : StackProg (Fin 32) BSym := pushProg (regPorts r) .one
def regPop (r : Fin 21) : StackProg (Fin 32) BSym := popProg (regPorts r)
def regAdd (dst src : Fin 21) : StackProg (Fin 32) BSym := copyProg (regPorts src) (regPorts dst) 20
def regAssign (dst src : Fin 21) : StackProg (Fin 32) BSym :=
  if dst = src then regKeep else .seq (regReset dst) (regAdd dst src)

theorem regKeep_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) :
    regKeep.Exec (regStore frame R) (regStore frame R) 1 := by
  have he : StackProg.applyAct (fun _ _ => StackAct.keep) (regStore frame R) = regStore frame R := by
    funext k
    rfl
  simpa only [regKeep, he] using StackProg.Exec.act (fun _ _ => StackAct.keep) (regStore frame R)

theorem regReset_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) :
    (regReset r).Exec (regStore frame R) (regStore frame (Function.update R r 0)) (3*(R r)+1) := by
  have he := (stack_basic_macros (regPorts r) (regStore frame R)).2.2
  rw [regStore_update]
  simpa [regReset] using he

theorem regInc_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) :
    (regInc r).Exec (regStore frame R) (regStore frame (Function.update R r (R r+1))) 1 := by
  have he := (stack_basic_macros (regPorts r) (regStore frame R)).1 BSym.one
  rw [regStore_update]
  simpa [regInc, List.replicate_succ] using he

theorem regPop_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) :
    (regPop r).Exec (regStore frame R) (regStore frame (Function.update R r (R r-1))) 1 := by
  have he := (stack_basic_macros (regPorts r) (regStore frame R)).2.1
  rw [regStore_update]
  simpa [regPop] using he

theorem regAdd_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (dst src : Fin 21)
    (h : dst ≠ src) :
    (regAdd dst src).Exec (regStore frame R)
      (regStore frame (Function.update R dst (R src + R dst))) (6*(R src)+3) := by
  have hsd : regPorts src ≠ regPorts dst := fun he => h (regPorts.injective he).symm
  have hst : regPorts src ≠ 20 := regScratch_outside 20 (by decide) src
  have hdt : regPorts dst ≠ 20 := regScratch_outside 20 (by decide) dst
  have he := stack_copy (regPorts src) (regPorts dst) 20 hsd hst hdt (regStore frame R)
    (regStore_scratch frame R 20 (by decide))
  have hu : Function.update (regStore frame R) (regPorts dst)
      (regStore frame R (regPorts src) ++ regStore frame R (regPorts dst)) =
      regStore frame (Function.update R dst (R src + R dst)) := by
    rw [regStore_update]
    simp
  rw [hu] at he
  simpa [regAdd] using he

theorem regAssign_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (dst src : Fin 21) :
    ∃ steps, (regAssign dst src).Exec (regStore frame R)
      (regStore frame (Function.update R dst (R src))) steps ∧ steps ≤ 10*(regSize R+1) := by
  by_cases h : dst = src
  · subst src
    have hu : Function.update R dst (R dst) = R := by
      funext r
      by_cases hr : r = dst <;> simp [hr]
    refine ⟨1, ?_, ?_⟩
    · simpa [regAssign, hu] using regKeep_exec frame R
    · omega
  · let S := Function.update R dst 0
    have hs : S src = R src := by simp [S, Ne.symm h]
    have hu : Function.update S dst (S src + S dst) = Function.update R dst (R src) := by
      funext r
      by_cases hr : r = dst <;> simp [S, hr, Ne.symm h]
    have he := StackProg.Exec.seq (regReset_exec frame R dst) (regAdd_exec frame S dst src h)
    rw [hu] at he
    refine ⟨(3*(R dst)+1)+1+(6*(S src)+3), ?_, ?_⟩
    · simpa [regAssign, h, S] using he
    · have hdst := reg_le_size R dst
      have hsrc := reg_le_size R src
      omega

def regIncs (r : Fin 21) : ℕ → StackProg (Fin 32) BSym
  | 0 => regKeep
  | n+1 => .seq (regInc r) (regIncs r n)

def regSetConst (r : Fin 21) (n : ℕ) : StackProg (Fin 32) BSym :=
  .seq (regReset r) (regIncs r n)

theorem regIncs_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) (n : ℕ) :
    (regIncs r n).Exec (regStore frame R) (regStore frame (Function.update R r (R r+n))) (2*n+1) := by
  induction n generalizing R with
  | zero =>
      have hu : Function.update R r (R r + 0) = R := by
        funext q
        by_cases hq : q = r <;> simp [hq]
      simpa [regIncs, hu] using regKeep_exec frame R
  | succ n ih =>
      have he := StackProg.Exec.seq (regInc_exec frame R r) (ih (Function.update R r (R r+1)))
      have hu : Function.update (Function.update R r (R r+1)) r
          ((Function.update R r (R r+1)) r+n) = Function.update R r (R r+(n+1)) := by
        funext q
        by_cases hq : q = r <;> simp [hq, Nat.add_comm, Nat.add_left_comm]
      rw [hu] at he
      convert he using 1 <;> first | rfl | omega

theorem regSetConst_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) (n : ℕ) :
    ∃ steps, (regSetConst r n).Exec (regStore frame R)
      (regStore frame (Function.update R r n)) steps ∧ steps ≤ 3*(R r)+2*n+5 := by
  have he := StackProg.Exec.seq (regReset_exec frame R r) (regIncs_exec frame (Function.update R r 0) r n)
  have hu : Function.update (Function.update R r 0) r ((Function.update R r 0) r+n) =
      Function.update R r n := by
    funext q
    by_cases hq : q = r <;> simp [hq]
  rw [hu] at he
  exact ⟨_, he, by omega⟩

end TensorNP.Encoder
end


/- Inlined module: RegisterBranch -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

noncomputable def branchEmbedding (r s : Fin 21) (hne : r ≠ s) : Fin 6 ↪ Fin 32 :=
  ⟨![regPorts r, regPorts s, 18, 25, 26, 19], by
    intro i j h
    have hrs : regPorts r ≠ regPorts s := fun he => hne (regPorts.injective he)
    have hr := regPorts_not_scratch r
    have hs := regPorts_not_scratch s
    simp only [regScratch, not_or] at hr hs
    fin_cases i <;> fin_cases j <;> simp_all⟩

private lemma register_write_update {M : ℕ} {A : Type} (r : Fin 6 ↪ Fin M)
    (t : Fin 6 → List A) (frame : Fin M → List A) (q : Fin 6) (v : List A) :
    Function.update (StackProgPortLift.write r t frame) (r q) v =
      StackProgPortLift.write r (Function.update t q v) frame := by
  classical
  funext l
  by_cases hex : ∃ k, r k = l
  · obtain ⟨k, rfl⟩ := hex
    by_cases hk : k = q
    · subst k
      simp [register_write_at]
    · have hneq : r k ≠ r q := fun h => hk (r.injective h)
      simp [register_write_at, hk, hneq]
  · have hout : ∀ k, r k ≠ l := by
      intro k hk
      exact hex ⟨k, hk⟩
    have hl : l ≠ r q := fun he => hex ⟨q, he.symm⟩
    rw [Function.update_of_ne hl, register_write_outside r t frame l hout,
      register_write_outside r (Function.update t q v) frame l hout]

private lemma register_compare_start (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) :
    StackProgPortLift.write (branchEmbedding r s hne) (compareStore (R r) (R s) 0 0 [])
      (regStore frame R) = regStore frame R := by
  funext l
  by_cases hex : ∃ k, branchEmbedding r s hne k = l
  · obtain ⟨k, rfl⟩ := hex
    rw [register_write_at]
    have h18 := regStore_scratch frame R 18 (by decide)
    have h19 := regStore_scratch frame R 19 (by decide)
    have h25 := regStore_scratch frame R 25 (by decide)
    have h26 := regStore_scratch frame R 26 (by decide)
    fin_cases k
    · exact (regStore_at frame R r).symm
    · exact (regStore_at frame R s).symm
    · exact h18.symm
    · exact h25.symm
    · exact h26.symm
    · exact h19.symm
  · have hout : ∀ k, branchEmbedding r s hne k ≠ l := by
      intro k hk
      exact hex ⟨k, hk⟩
    exact register_write_outside _ _ _ _ hout

private noncomputable def comparisonState (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) : Fin 32 → List BSym :=
  StackProgPortLift.write (branchEmbedding r s hne) (compareStore (R r) (R s) left right flags)
    (regStore frame R)

private lemma comparisonState_clear18 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    Function.update (comparisonState r s hne frame R left right flags) 18 [] =
      comparisonState r s hne frame R 0 right flags := by
  change Function.update (StackProgPortLift.write (branchEmbedding r s hne)
    (compareStore (R r) (R s) left right flags) (regStore frame R)) (branchEmbedding r s hne 2) [] = _
  rw [register_write_update]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma comparisonState_clear25 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    Function.update (comparisonState r s hne frame R left right flags) 25 [] =
      comparisonState r s hne frame R left 0 flags := by
  change Function.update (StackProgPortLift.write (branchEmbedding r s hne)
    (compareStore (R r) (R s) left right flags) (regStore frame R)) (branchEmbedding r s hne 3) [] = _
  rw [register_write_update]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma comparisonState_clear19 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    Function.update (comparisonState r s hne frame R left right flags) 19 [] =
      comparisonState r s hne frame R left right [] := by
  change Function.update (StackProgPortLift.write (branchEmbedding r s hne)
    (compareStore (R r) (R s) left right flags) (regStore frame R)) (branchEmbedding r s hne 5) [] = _
  rw [register_write_update]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma comparisonState_at18 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    comparisonState r s hne frame R left right flags 18 = List.replicate left .one := by
  change StackProgPortLift.write (branchEmbedding r s hne) _ _ (branchEmbedding r s hne 2) = _
  rw [register_write_at]
  rfl

private lemma comparisonState_at25 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    comparisonState r s hne frame R left right flags 25 = List.replicate right .one := by
  change StackProgPortLift.write (branchEmbedding r s hne) _ _ (branchEmbedding r s hne 3) = _
  rw [register_write_at]
  rfl

private lemma comparisonState_at19 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    comparisonState r s hne frame R left right flags 19 = flags := by
  change StackProgPortLift.write (branchEmbedding r s hne) _ _ (branchEmbedding r s hne 5) = _
  rw [register_write_at]
  rfl

private def branchCleanup : StackProg (Fin 32) BSym :=
  .seq (clearProg 18) (.seq (clearProg 25) (clearProg 19))

private lemma branchCleanup_exec (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    branchCleanup.Exec (comparisonState r s hne frame R left right flags) (regStore frame R)
      (3 * left + 3 * right + 3 * flags.length + 5) := by
  have he1 := (stack_basic_macros (18 : Fin 32) (comparisonState r s hne frame R left right flags)).2.2
  rw [comparisonState_clear18, comparisonState_at18, List.length_replicate] at he1
  have he2 := (stack_basic_macros (25 : Fin 32) (comparisonState r s hne frame R 0 right flags)).2.2
  rw [comparisonState_clear25, comparisonState_at25, List.length_replicate] at he2
  have he3 := (stack_basic_macros (19 : Fin 32) (comparisonState r s hne frame R 0 0 flags)).2.2
  rw [comparisonState_clear19, comparisonState_at19] at he3
  have hend : comparisonState r s hne frame R 0 0 [] = regStore frame R :=
    register_compare_start r s hne frame R
  rw [hend] at he3
  have he := StackProg.Exec.seq he1 (StackProg.Exec.seq he2 he3)
  convert he using 1 <;> first | rfl | omega

private lemma comparisonState_pop19 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (a b : BSym) :
    (popProg 19).Exec (comparisonState r s hne frame R left right [a,b])
      (comparisonState r s hne frame R left right [b]) 1 := by
  have he := (stack_basic_macros (19 : Fin 32)
    (comparisonState r s hne frame R left right [a,b])).2.1
  rw [comparisonState_at19] at he
  simp only [List.tail_cons] at he
  have heq : Function.update (comparisonState r s hne frame R left right [a,b]) 19 [b] =
      comparisonState r s hne frame R left right [b] := by
    change Function.update (StackProgPortLift.write (branchEmbedding r s hne)
      (compareStore (R r) (R s) left right [a,b]) (regStore frame R)) (branchEmbedding r s hne 5) [b] = _
    rw [register_write_update]
    apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
    funext k
    fin_cases k <;> simp [Function.update, compareStore]
  rw [heq] at he
  exact he

private def branchSkip : StackProg (Fin 32) BSym := .act (fun _ _ => .keep)
private def branchFlagTest (h : Fin 32 → Option BSym) : Bool := h 19 == some .one
private def branchPrep (less : Bool) : StackProg (Fin 32) BSym :=
  if less then popProg 19 else branchSkip

noncomputable def regBranch (less : Bool) (r s : Fin 21)
    (yes no : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym := by
  classical
  exact if heq : r = s then (if less then no else yes) else
    .seq (Classical.choose (unary_compare_framed 32 (branchEmbedding r s heq)))
      (.seq (branchPrep less) (.branch branchFlagTest (.seq branchCleanup yes) (.seq branchCleanup no)))

private def eqBit (x y : ℕ) : BSym := if x = y then .one else .zero
private def ltBit (x y : ℕ) : BSym := if x < y then .one else .zero
private def testedFlags (less : Bool) (x y : ℕ) : List BSym :=
  if less then [ltBit x y] else [eqBit x y, ltBit x y]

private lemma branchPrep_exec (less : Bool) (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) :
    (branchPrep less).Exec
      (comparisonState r s hne frame R left right [eqBit (R r) (R s), ltBit (R r) (R s)])
      (comparisonState r s hne frame R left right (testedFlags less (R r) (R s))) 1 := by
  cases less with
  | false =>
      let store := comparisonState r s hne frame R left right [eqBit (R r) (R s), ltBit (R r) (R s)]
      have hid : StackProg.applyAct (fun _ _ => StackAct.keep) store = store := by
        funext k
        rfl
      simpa only [branchPrep, testedFlags, Bool.false_eq_true, ↓reduceIte, branchSkip, hid] using
        (StackProg.Exec.act (fun _ _ => StackAct.keep) store)
  | true =>
      exact comparisonState_pop19 r s hne frame R left right (eqBit (R r) (R s)) (ltBit (R r) (R s))

private lemma branchFlagTest_correct (less : Bool) (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) :
    branchFlagTest (fun k => (comparisonState r s hne frame R left right
      (testedFlags less (R r) (R s)) k).head?) =
      decide (if less then R r < R s else R r = R s) := by
  unfold branchFlagTest
  dsimp only
  rw [comparisonState_at19]
  cases less with
  | false => by_cases h : R r = R s <;> simp [testedFlags, eqBit, h]
  | true => by_cases h : R r < R s <;> simp [testedFlags, ltBit, h]

private lemma branchAfter_exec (less : Bool) (r s : Fin 21) (hne : r ≠ s)
    (yes no : StackProg (Fin 32) BSym) (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ)
    (T : Fin 32 → List BSym) (n left right : ℕ)
    (ha : (if (if less then R r < R s else R r = R s) then yes else no).Exec (regStore frame R) T n) :
    ∃ m, (StackProg.seq (branchPrep less)
      (.branch branchFlagTest (.seq branchCleanup yes) (.seq branchCleanup no))).Exec
      (comparisonState r s hne frame R left right [eqBit (R r) (R s), ltBit (R r) (R s)]) T m ∧
      m ≤ 3 * left + 3 * right + 15 + n := by
  let flags := testedFlags less (R r) (R s)
  have hf : flags.length ≤ 2 := by cases less <;> simp [flags, testedFlags]
  have heP := branchPrep_exec less r s hne frame R left right
  have heC := branchCleanup_exec r s hne frame R left right flags
  have ht := branchFlagTest_correct less r s hne frame R left right
  by_cases h : (if less then R r < R s else R r = R s)
  · have htest : branchFlagTest (fun k => (comparisonState r s hne frame R left right flags k).head?) = true := by
      simpa [flags, h] using ht
    have hy : yes.Exec (regStore frame R) T n := by simpa [h] using ha
    have heArm := StackProg.Exec.seq heC hy
    have heB := StackProg.Exec.branchTrue (q := .seq branchCleanup no) htest heArm
    have he := StackProg.Exec.seq heP heB
    refine ⟨_, he, ?_⟩
    omega
  · have htest : branchFlagTest (fun k => (comparisonState r s hne frame R left right flags k).head?) = false := by
      simpa [flags, h] using ht
    have hn : no.Exec (regStore frame R) T n := by simpa [h] using ha
    have heArm := StackProg.Exec.seq heC hn
    have heB := StackProg.Exec.branchFalse (p := .seq branchCleanup yes) htest heArm
    have he := StackProg.Exec.seq heP heB
    refine ⟨_, he, ?_⟩
    omega

theorem regBranch_exec (less : Bool) (r s : Fin 21) (yes no : StackProg (Fin 32) BSym)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (T : Fin 32 → List BSym) (n : ℕ)
    (ha : (if (if less then R r < R s else R r = R s) then yes else no).Exec (regStore frame R) T n) :
    ∃ m, (regBranch less r s yes no).Exec (regStore frame R) T m ∧
      m ≤ 100 * (regSize R + 1) + n := by
  classical
  by_cases heq : r = s
  · subst s
    cases less with
    | false =>
        refine ⟨n, ?_, by omega⟩
        simpa [regBranch] using ha
    | true =>
        refine ⟨n, ?_, by omega⟩
        simpa [regBranch] using ha
  · have hc := Classical.choose_spec (unary_compare_framed 32 (branchEmbedding r s heq))
    obtain ⟨ct, heC, hct⟩ := hc (R r) (R s) (regStore frame R)
    have heC' : (Classical.choose (unary_compare_framed 32 (branchEmbedding r s heq))).Exec
        (regStore frame R)
        (comparisonState r s heq frame R (R r - R s) (R s - R r)
          [eqBit (R r) (R s), ltBit (R r) (R s)]) ct := by
      simpa only [register_compare_start, comparisonState, eqBit, ltBit] using heC
    obtain ⟨bt, heB, hbt⟩ := branchAfter_exec less r s heq yes no frame R T n
      (R r - R s) (R s - R r) ha
    have he := StackProg.Exec.seq heC' heB
    refine ⟨ct + 1 + bt, ?_, ?_⟩
    · simpa only [regBranch, dif_neg heq] using he
    · have hr := reg_le_size R r
      have hs := reg_le_size R s
      omega

private lemma transfer_to_update (src dst : Fin 32) (hne : dst ≠ src) (store : Fin 32 → List BSym) :
    transferStore src (fun k => decide (k = dst)) store =
      Function.update (Function.update store src []) dst ((store src).reverse ++ store dst) := by
  classical
  funext k
  by_cases hsrc : k = src <;> by_cases hdst : k = dst <;>
    simp [transferStore, Function.update, hsrc, hdst, hne, Ne.symm hne] at *

noncomputable def regSub (dst src : Fin 21) : StackProg (Fin 32) BSym := by
  classical
  exact if heq : dst = src then clearProg (regPorts dst) else
    .seq (Classical.choose (unary_compare_framed 32 (branchEmbedding dst src heq)))
      (.seq (clearProg (regPorts dst))
        (.seq (transferProg 18 (fun k => decide (k = regPorts dst)))
          (.seq (clearProg 25) (clearProg 19))))


private noncomputable def changedState (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x left right : ℕ)
    (flags : List BSym) : Fin 32 → List BSym :=
  StackProgPortLift.write (branchEmbedding r s hne) (compareStore x (R s) left right flags)
    (regStore frame R)

private lemma changedState_set (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x left right : ℕ) (flags : List BSym)
    (q : Fin 6) (v : List BSym) :
    Function.update (changedState r s hne frame R x left right flags) (branchEmbedding r s hne q) v =
      StackProgPortLift.write (branchEmbedding r s hne)
        (Function.update (compareStore x (R s) left right flags) q v) (regStore frame R) := by
  exact register_write_update _ _ _ _ _

private lemma changedState_setdst (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x y left right : ℕ) (flags : List BSym) :
    Function.update (changedState r s hne frame R x left right flags) (regPorts r)
      (List.replicate y .one) = changedState r s hne frame R y left right flags := by
  change Function.update _ (branchEmbedding r s hne 0) _ = _
  rw [changedState_set]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma changedState_clear18 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x left right : ℕ) (flags : List BSym) :
    Function.update (changedState r s hne frame R x left right flags) 18 [] =
      changedState r s hne frame R x 0 right flags := by
  change Function.update _ (branchEmbedding r s hne 2) _ = _
  rw [changedState_set]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma changedState_clear25 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x left right : ℕ) (flags : List BSym) :
    Function.update (changedState r s hne frame R x left right flags) 25 [] =
      changedState r s hne frame R x left 0 flags := by
  change Function.update _ (branchEmbedding r s hne 3) _ = _
  rw [changedState_set]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma changedState_clear19 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x left right : ℕ) (flags : List BSym) :
    Function.update (changedState r s hne frame R x left right flags) 19 [] =
      changedState r s hne frame R x left right [] := by
  change Function.update _ (branchEmbedding r s hne 5) _ = _
  rw [changedState_set]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma changedState_end (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x : ℕ) :
    changedState r s hne frame R x 0 0 [] = regStore frame (Function.update R r x) := by
  rw [regStore_update]
  rw [← register_compare_start r s hne frame R]
  change _ = Function.update _ (branchEmbedding r s hne 0) _
  rw [register_write_update]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]


private lemma changedState_at (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x left right : ℕ) (flags : List BSym)
    (q : Fin 6) :
    changedState r s hne frame R x left right flags (branchEmbedding r s hne q) =
      compareStore x (R s) left right flags q := by
  exact register_write_at _ _ _ _

private lemma subAfter_exec (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    (StackProg.seq (clearProg (regPorts r))
      (.seq (transferProg 18 (fun k => decide (k = regPorts r)))
        (.seq (clearProg 25) (clearProg 19)))).Exec
      (changedState r s hne frame R (R r) left right flags)
      (regStore frame (Function.update R r left))
      (3 * R r + 3 * left + 3 * right + 3 * flags.length + 7) := by
  have he1 := (stack_basic_macros (regPorts r) (changedState r s hne frame R (R r) left right flags)).2.2
  have hv1 : changedState r s hne frame R (R r) left right flags (regPorts r) = List.replicate (R r) .one := by
    change changedState r s hne frame R (R r) left right flags (branchEmbedding r s hne 0) = _
    rw [changedState_at]
    rfl
  rw [show ([] : List BSym) = List.replicate 0 .one from rfl, changedState_setdst, hv1, List.length_replicate] at he1
  have ht := stack_transfer (18 : Fin 32) (fun k => decide (k = regPorts r))
    (changedState r s hne frame R 0 left right flags)
  have hp18 : changedState r s hne frame R 0 left right flags 18 = List.replicate left .one := by
    change changedState r s hne frame R 0 left right flags (branchEmbedding r s hne 2) = _
    rw [changedState_at]
    rfl
  have hpdst : changedState r s hne frame R 0 left right flags (regPorts r) = [] := by
    change changedState r s hne frame R 0 left right flags (branchEmbedding r s hne 0) = _
    rw [changedState_at]
    rfl
  have hne18 : regPorts r ≠ (18 : Fin 32) := by
    intro h
    apply regPorts_not_scratch r
    rw [h]
    decide
  rw [transfer_to_update 18 (regPorts r) hne18, hp18, hpdst, List.reverse_replicate,
    List.append_nil, changedState_clear18, changedState_setdst, List.length_replicate] at ht
  have he2 := (stack_basic_macros (25 : Fin 32) (changedState r s hne frame R left 0 right flags)).2.2
  have hp25 : changedState r s hne frame R left 0 right flags 25 = List.replicate right .one := by
    change changedState r s hne frame R left 0 right flags (branchEmbedding r s hne 3) = _
    rw [changedState_at]
    rfl
  rw [changedState_clear25, hp25, List.length_replicate] at he2
  have he3 := (stack_basic_macros (19 : Fin 32) (changedState r s hne frame R left 0 0 flags)).2.2
  have hp19 : changedState r s hne frame R left 0 0 flags 19 = flags := by
    change changedState r s hne frame R left 0 0 flags (branchEmbedding r s hne 5) = _
    rw [changedState_at]
    rfl
  rw [changedState_clear19, changedState_end, hp19] at he3
  have he := StackProg.Exec.seq he1 (StackProg.Exec.seq ht (StackProg.Exec.seq he2 he3))
  convert he using 1; first | rfl | omega

theorem regSub_exec (dst src : Fin 21) (hne : dst ≠ src)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) :
    ∃ m, (regSub dst src).Exec (regStore frame R)
      (regStore frame (Function.update R dst (R dst - R src))) m ∧
      m ≤ 100 * (regSize R + 1) := by
  classical
  have hc := Classical.choose_spec (unary_compare_framed 32 (branchEmbedding dst src hne))
  obtain ⟨ct, heC, hct⟩ := hc (R dst) (R src) (regStore frame R)
  have heC' : (Classical.choose (unary_compare_framed 32 (branchEmbedding dst src hne))).Exec
      (regStore frame R)
      (changedState dst src hne frame R (R dst) (R dst - R src) (R src - R dst)
        [eqBit (R dst) (R src), ltBit (R dst) (R src)]) ct := by
    simpa only [register_compare_start, changedState, eqBit, ltBit] using heC
  have heA := subAfter_exec dst src hne frame R (R dst - R src) (R src - R dst)
    [eqBit (R dst) (R src), ltBit (R dst) (R src)]
  have he := StackProg.Exec.seq heC' heA
  refine ⟨ct + 1 + (3 * R dst + 3 * (R dst - R src) + 3 * (R src - R dst) + 3 * 2 + 7), ?_, ?_⟩
  · simpa only [regSub, dif_neg hne, List.length_cons, List.length_nil] using he
  · have hr := reg_le_size R dst
    have hs := reg_le_size R src
    simp only [List.length_cons, List.length_nil] at *
    omega

end TensorNP.Encoder
end


/- Inlined module: RegisterNeighbor -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def regNeighborPorts : Fin 8 ↪ Fin 32 := ⟨![7,1,6,12,18,20,21,22], by decide⟩
def regNeighborDecode (l : Fin 32) : Option (Fin 8) :=
  if l = 7 then some 0 else if l = 1 then some 1 else if l = 6 then some 2
  else if l = 12 then some 3 else if l = 18 then some 4 else if l = 20 then some 5
  else if l = 21 then some 6 else if l = 22 then some 7 else none

lemma regNeighborDecode_spec (l : Fin 32) (k : Fin 8) :
    regNeighborDecode l = some k ↔ regNeighborPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

noncomputable def regNeighborWork (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (out : List BSym) : Fin 32 → List BSym :=
  Function.update (regStore frame R) 18 out

def regNeighborGuard (h : Fin 32 → Option BSym) : Bool := h 18 == some .one

def regNeighborBranch (yes no : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .seq (StackProgPortLift.liftProgC regNeighborPorts regNeighborDecode TensorAdjacencyLookup8.lookupProg)
    (.branch regNeighborGuard (.seq (popProg 18) yes) (.seq (popProg 18) no))

lemma regStore_data (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) : regStore frame R 7 = frame 7 := by
  rw [regStore, port_write_outside]
  · rfl
  · intro r
    fin_cases r <;> decide

lemma regNeighbor_project (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (out : List BSym) :
    StackProgPortLift.project regNeighborPorts (regNeighborWork frame R out) =
      TensorAdjacencyLookup8.store (frame 7) (List.replicate (R 0) .one)
        (List.replicate (R 3) .one) (List.replicate (R 8) .one) out [] [] [] := by
  have h1 : regStore frame R 1 = List.replicate (R 0) .one := regStore_at frame R 0
  have h6 : regStore frame R 6 = List.replicate (R 3) .one := regStore_at frame R 3
  have h12 : regStore frame R 12 = List.replicate (R 8) .one := regStore_at frame R 8
  have h20 := regStore_scratch frame R 20 (by decide)
  have h21 := regStore_scratch frame R 21 (by decide)
  have h22 := regStore_scratch frame R 22 (by decide)
  funext k
  fin_cases k <;> simp [StackProgPortLift.project, regNeighborPorts, regNeighborWork,
    TensorAdjacencyLookup8.store, regStore_data, h1, h6, h12, h20, h21, h22]

lemma regNeighborWork_empty (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) :
    regNeighborWork frame R [] = regStore frame R := by
  have h18 := regStore_scratch frame R 18 (by decide)
  funext l
  by_cases hl : l = 18 <;> simp [regNeighborWork, hl, h18]

lemma regNeighbor_write (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (a : BSym) :
    StackProgPortLift.write regNeighborPorts
      (TensorAdjacencyLookup8.store (frame 7) (List.replicate (R 0) .one)
        (List.replicate (R 3) .one) (List.replicate (R 8) .one) [a] [] [] [])
      (regStore frame R) = regNeighborWork frame R [a] := by
  classical
  funext l
  by_cases hl : ∃ k, regNeighborPorts k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [port_write_at]
    exact (congrFun (regNeighbor_project frame R [a]) k).symm
  · have h18 : l ≠ 18 := by intro h; apply hl; exact ⟨4, h.symm⟩
    simp [StackProgPortLift.write, hl, regNeighborWork, h18]

lemma regNeighborPop (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (a : BSym) :
    (popProg (18 : Fin 32)).Exec (regNeighborWork frame R [a]) (regStore frame R) 1 := by
  have h18 := regStore_scratch frame R 18 (by decide)
  have hu : Function.update (regNeighborWork frame R [a]) 18
      ((regNeighborWork frame R [a]) 18).tail = regStore frame R := by
    funext l
    by_cases hl : l = 18 <;> simp [regNeighborWork, hl, h18]
  simpa only [hu] using (stack_basic_macros (18 : Fin 32) (regNeighborWork frame R [a])).2.1

theorem regNeighborBranch_exec (yes no : StackProg (Fin 32) BSym)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (T : Fin 32 → List BSym) (n : ℕ)
    (hrow : R 3 < R 0) (hcol : R 8 < R 0) (hlen : (frame 7).length = R 0 * R 0)
    (harm : (if (frame 7).getD (R 3 * R 0 + R 8) .zero = .one then yes else no).Exec
      (regStore frame R) T n) :
    ∃ m, (regNeighborBranch yes no).Exec (regStore frame R) T m ∧
      m ≤ 100*(R 0+1)^2+n := by
  let a := (frame 7).getD (R 3 * R 0 + R 8) BSym.zero
  change (if a = .one then yes else no).Exec (regStore frame R) T n at harm
  obtain ⟨steps, hbound, he⟩ := TensorAdjacencyLookup8.lookupProg_exec (R 0) (R 3) (R 8)
    (frame 7) [] hrow hcol hlen
  have hproject : StackProgPortLift.project regNeighborPorts (regStore frame R) =
      TensorAdjacencyLookup8.store (frame 7) (List.replicate (R 0) .one)
        (List.replicate (R 3) .one) (List.replicate (R 8) .one) [] [] [] [] := by
    simpa only [regNeighborWork_empty] using regNeighbor_project frame R []
  have hlift := StackProgPortLift.liftProgC_exec regNeighborPorts regNeighborDecode
    regNeighborDecode_spec he (regStore frame R) hproject
  rw [regNeighbor_write] at hlift
  have hsq : 1 ≤ (R 0+1)^2 := Nat.one_le_pow 2 (R 0+1) (by omega)
  by_cases ha : a = .one
  · have hy : yes.Exec (regStore frame R) T n := by simpa [ha] using harm
    have hg : regNeighborGuard (fun k => (regNeighborWork frame R [a] k).head?) = true := by
      simp [regNeighborGuard, regNeighborWork, ha]
    have hb := StackProg.Exec.branchTrue (test := regNeighborGuard) (q := .seq (popProg 18) no)
      hg (StackProg.Exec.seq (regNeighborPop frame R a) hy)
    have ht := StackProg.Exec.seq hlift hb
    refine ⟨steps+1+(1+(1+1+n)), ht, ?_⟩
    omega
  · have hn : no.Exec (regStore frame R) T n := by simpa [ha] using harm
    have hg : regNeighborGuard (fun k => (regNeighborWork frame R [a] k).head?) = false := by
      simp [regNeighborGuard, regNeighborWork, ha]
    have hb := StackProg.Exec.branchFalse (test := regNeighborGuard) (p := .seq (popProg 18) yes)
      hg (StackProg.Exec.seq (regNeighborPop frame R a) hn)
    have ht := StackProg.Exec.seq hlift hb
    refine ⟨steps+1+(1+(1+1+n)), ht, ?_⟩
    omega

end TensorNP.Encoder
end


/- Inlined module: ActualCounterBackend -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

noncomputable def actualRegBackend : RegBackend where
  keep := regKeep
  reset := regReset
  inc := regInc
  assign := regAssign
  add := fun dst src _ => regAdd dst src
  sub := fun dst src _ => regSub dst src
  branch := regBranch
  neighbor := regNeighborBranch
  keep_ok := regKeep_exec
  reset_ok := by
    intro frame R r
    refine ⟨3 * R r + 1, regReset_exec frame R r, ?_⟩
    have hr := reg_le_size R r
    simp only [regCharge]
    omega
  inc_ok := by
    intro frame R r
    refine ⟨1, regInc_exec frame R r, ?_⟩
    simp only [regCharge]
    omega
  assign_ok := by
    intro frame R dst src
    obtain ⟨n, hn, hbound⟩ := regAssign_exec frame R dst src
    refine ⟨n, hn, ?_⟩
    simp only [regCharge]
    omega
  add_ok := by
    intro frame R dst src h
    refine ⟨6 * R src + 3, regAdd_exec frame R dst src h, ?_⟩
    have hs := reg_le_size R src
    simp only [regCharge]
    omega
  sub_ok := by
    intro frame R dst src h
    exact regSub_exec dst src h frame R
  pop_ok := regPop_exec
  branch_ok := by
    intro less r s yes no frame R T n harm
    apply regBranch_exec less r s yes no frame R T n
    cases less <;> simpa only [regCompare, Bool.false_eq_true, ↓reduceIte,
      decide_eq_true_eq] using harm
  neighbor_ok := by
    intro yes no frame R T n hr hc hlen harm
    apply regNeighborBranch_exec yes no frame R T n hr hc hlen
    simpa only [regNeighbor, decide_eq_true_eq] using harm

theorem actual_compileReg_sound {data : List BSym} {p : RegCmd} {R T : RegFile} {n : ℕ}
    (h : RegExec data p R T n) (frame : Fin 32 → List BSym) (hdata : frame 7 = data) :
    ∃ m, (compileReg actualRegBackend p).Exec (regStore frame R) (regStore frame T) m ∧ m ≤ n := by
  exact compileReg_sound actualRegBackend h frame hdata

end TensorNP.Encoder
end


/- Inlined module: Compare32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def comparePorts32 : Fin 6 ↪ Fin 32 := ⟨![23, 24, 18, 25, 26, 19], by decide⟩

def compareDecode32 (l : Fin 32) : Option (Fin 6) :=
  if l = 23 then some 0 else if l = 24 then some 1 else if l = 18 then some 2
  else if l = 25 then some 3 else if l = 26 then some 4 else if l = 19 then some 5 else none

lemma compareDecode32_spec (l : Fin 32) (k : Fin 6) :
    compareDecode32 l = some k ↔ comparePorts32 k = l := by
  fin_cases l <;> fin_cases k <;> decide

def compareFrameStore32 (x y left right : ℕ) (flags : List BSym)
    (frame : Fin 32 → List BSym) : Fin 32 → List BSym :=
  fun k => if k = 23 then List.replicate x .one else if k = 24 then List.replicate y .one
    else if k = 18 then List.replicate left .one else if k = 25 then List.replicate right .one
    else if k = 26 then [] else if k = 19 then flags else frame k

lemma compareFrameStore32_project (x y left right : ℕ) (flags : List BSym)
    (frame : Fin 32 → List BSym) :
    StackProgPortLift.project comparePorts32 (compareFrameStore32 x y left right flags frame) =
      compareStore x y left right flags := by
  funext k
  fin_cases k <;> rfl

private lemma compare_write_at (t : Fin 6 → List BSym) (s : Fin 32 → List BSym) (k : Fin 6) :
    StackProgPortLift.write comparePorts32 t s (comparePorts32 k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := comparePorts32.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma compareFrameStore32_write (x y left right left' right' : ℕ) (flags flags' : List BSym)
    (frame : Fin 32 → List BSym) :
    StackProgPortLift.write comparePorts32 (compareStore x y left' right' flags')
      (compareFrameStore32 x y left right flags frame) =
      compareFrameStore32 x y left' right' flags' frame := by
  classical
  funext l
  by_cases hl : ∃ k, comparePorts32 k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [compare_write_at]
    exact (congrFun (compareFrameStore32_project x y left' right' flags' frame) k).symm
  · have h23 : l ≠ 23 := by
      intro he
      apply hl
      exact ⟨0, he.symm⟩
    have h24 : l ≠ 24 := by
      intro he
      apply hl
      exact ⟨1, he.symm⟩
    have h18 : l ≠ 18 := by
      intro he
      apply hl
      exact ⟨2, he.symm⟩
    have h25 : l ≠ 25 := by
      intro he
      apply hl
      exact ⟨3, he.symm⟩
    have h26 : l ≠ 26 := by
      intro he
      apply hl
      exact ⟨4, he.symm⟩
    have h19 : l ≠ 19 := by
      intro he
      apply hl
      exact ⟨5, he.symm⟩
    simp [StackProgPortLift.write, hl, compareFrameStore32, h23, h24, h18, h25, h26, h19]

theorem unary_compare32 : ∃ p : StackProg (Fin 32) BSym,
    ∀ (x y : ℕ) (frame : Fin 32 → List BSym), ∃ steps,
      p.Exec (compareFrameStore32 x y 0 0 [] frame)
        (compareFrameStore32 x y (x-y) (y-x)
          [if x=y then BSym.one else .zero, if x<y then BSym.one else .zero] frame) steps ∧
      steps ≤ 10 * (x + y + 2) := by
  obtain ⟨p, hp⟩ := unary_compare_machine
  refine ⟨StackProgPortLift.liftProgC comparePorts32 compareDecode32 p, ?_⟩
  intro x y frame
  obtain ⟨steps, he, hb⟩ := hp x y
  refine ⟨steps, ?_, hb⟩
  have he' := StackProgPortLift.liftProgC_exec comparePorts32 compareDecode32
    compareDecode32_spec he (compareFrameStore32 x y 0 0 [] frame)
    (compareFrameStore32_project x y 0 0 [] frame)
  rw [compareFrameStore32_write] at he'
  exact he'

end TensorNP.Encoder
end


/- Inlined module: Magnitude32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def magnitude (x y : ℕ) : ℕ := if x < y then y - x else x - y

theorem magnitude_le (x y : ℕ) : magnitude x y ≤ x + y := by
  unfold magnitude
  split_ifs <;> omega

theorem magnitude_value (x y : ℕ) :
    (if x < y then -(magnitude x y : ℚ) else (magnitude x y : ℚ)) = (x : ℚ) - (y : ℚ) := by
  by_cases h : x < y
  · simp only [magnitude, h, if_true]
    rw [Nat.cast_sub (by omega : x ≤ y)]
    ring
  · simp only [magnitude, h, if_false]
    rw [Nat.cast_sub (by omega : y ≤ x)]

private def magnitudeTest (h : Fin 32 → Option BSym) : Bool := h 19 == some .one
private def magnitudeTransfer : StackProg (Fin 32) BSym :=
  transferProg 25 (fun k => decide (k = 18))
private def magnitudeKeep : StackProg (Fin 32) BSym := .act (fun _ _ => .keep)
private def magnitudeProgram (compare : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .seq compare (.seq (popProg 19) (.branch magnitudeTest magnitudeTransfer magnitudeKeep))

private lemma popFlag_exec (x y left right : ℕ) (eqFlag ltFlag : BSym)
    (frame : Fin 32 → List BSym) :
    (popProg 19).Exec (compareFrameStore32 x y left right [eqFlag, ltFlag] frame)
      (compareFrameStore32 x y left right [ltFlag] frame) 1 := by
  have heq : StackProg.applyAct (fun _ k => if k = 19 then .pop else .keep)
      (compareFrameStore32 x y left right [eqFlag, ltFlag] frame) =
      compareFrameStore32 x y left right [ltFlag] frame := by
    funext k
    fin_cases k <;> rfl
  simpa only [popProg, heq] using (StackProg.Exec.act
    (fun _ k => if k = 19 then .pop else .keep)
    (compareFrameStore32 x y left right [eqFlag, ltFlag] frame))

private lemma transferMagnitude_exec (x y right : ℕ) (flags : List BSym)
    (frame : Fin 32 → List BSym) :
    magnitudeTransfer.Exec (compareFrameStore32 x y 0 right flags frame)
      (compareFrameStore32 x y right 0 flags frame) (3 * right + 1) := by
  have he := stack_transfer (25 : Fin 32) (fun k => decide (k = 18))
    (compareFrameStore32 x y 0 right flags frame)
  have heq : transferStore (25 : Fin 32) (fun k => decide (k = 18))
      (compareFrameStore32 x y 0 right flags frame) = compareFrameStore32 x y right 0 flags frame := by
    funext k
    fin_cases k <;> simp [transferStore, compareFrameStore32]
  rw [heq] at he
  simpa [magnitudeTransfer, compareFrameStore32] using he

private lemma magnitudeBranch_exec (x y : ℕ) (frame : Fin 32 → List BSym) :
    ∃ steps, (StackProg.branch magnitudeTest magnitudeTransfer magnitudeKeep).Exec
      (compareFrameStore32 x y (x-y) (y-x) [if x < y then BSym.one else .zero] frame)
      (compareFrameStore32 x y (magnitude x y) 0 [if x < y then BSym.one else .zero] frame) steps ∧
      steps ≤ 3 * (x + y) + 2 := by
  by_cases h : x < y
  · have hx : x - y = 0 := by omega
    have ht : magnitudeTest (fun k => (compareFrameStore32 x y 0 (y-x) [.one] frame k).head?) = true := by
      rfl
    have he := StackProg.Exec.branchTrue (q := magnitudeKeep) ht
      (transferMagnitude_exec x y (y-x) [.one] frame)
    refine ⟨1 + (3 * (y-x) + 1), ?_, by omega⟩
    simpa [h, hx, magnitude] using he
  · have hy : y - x = 0 := by omega
    let s := compareFrameStore32 x y (x-y) 0 [.zero] frame
    have ht : magnitudeTest (fun k => (s k).head?) = false := by rfl
    have hk : magnitudeKeep.Exec s s 1 := by
      have hid : StackProg.applyAct (fun _ _ => StackAct.keep) s = s := by
        funext k
        rfl
      simpa only [magnitudeKeep, hid] using (StackProg.Exec.act (fun _ _ => StackAct.keep) s)
    have he := StackProg.Exec.branchFalse (p := magnitudeTransfer) ht hk
    refine ⟨2, ?_, by omega⟩
    simpa [s, h, hy, magnitude] using he

theorem magnitude32 : ∃ p : StackProg (Fin 32) BSym,
    ∀ (x y : ℕ) (frame : Fin 32 → List BSym), ∃ steps,
      p.Exec (compareFrameStore32 x y 0 0 [] frame)
        (compareFrameStore32 x y (magnitude x y) 0
          [if x < y then BSym.one else .zero] frame) steps ∧
      steps ≤ 20 * (x + y + 2) := by
  obtain ⟨compare, hc⟩ := unary_compare32
  refine ⟨magnitudeProgram compare, ?_⟩
  intro x y frame
  obtain ⟨ct, heC, hct⟩ := hc x y frame
  have heP := popFlag_exec x y (x-y) (y-x)
    (if x = y then BSym.one else .zero) (if x < y then BSym.one else .zero) frame
  obtain ⟨bt, heB, hbt⟩ := magnitudeBranch_exec x y frame
  have he := StackProg.Exec.seq heC (StackProg.Exec.seq heP heB)
  refine ⟨ct + 1 + (1 + 1 + bt), he, ?_⟩
  omega

end TensorNP.Encoder
end


/- Inlined module: IntegerWriter12 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def integerFrame12 (negative : Bool) (frame : Fin 7 → List BSym) : Fin 7 → List BSym :=
  fun k => if k = 5 then [if negative then BSym.one else .zero] else frame k

def integerStore12 (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 7 → List BSym) : Fin 12 → List BSym :=
  writerStore12 n tail (integerFrame12 negative frame)

private lemma integer_encoding (n : ℕ) (negative : Bool) :
    TensorNP.Eigen.encRat (if negative then -(n : ℚ) else (n : ℚ)) =
      (if negative && decide (0 < n) then [BSym.minus] else []) ++ encNat n ++ encNat 1 := by
  cases negative with
  | false =>
      simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte, TensorNP.Eigen.encRat,
        Rat.num_natCast, Rat.den_natCast, encInt, Int.natAbs_natCast]
      simp
  | true =>
      simp only [Bool.true_and, ↓reduceIte, TensorNP.Eigen.encRat,
        Rat.num_neg_eq_neg_num, Rat.num_natCast, Rat.den_neg_eq_den, Rat.den_natCast,
        encInt, Int.natAbs_neg, Int.natAbs_natCast]
      simp

private def integerSignTest (h : Fin 12 → Option BSym) : Bool :=
  (h 10 == some .one) && (h 0).isSome

private def integerKeep : StackProg (Fin 12) BSym := .act (fun _ _ => .keep)

private def integerProgram (writer : StackProg (Fin 12) BSym) : StackProg (Fin 12) BSym :=
  .seq (pushProg 1 .sep) (.seq (pushProg 1 .one)
    (.seq writer (.branch integerSignTest (pushProg 1 .minus) integerKeep)))

private lemma integerStore_push (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 7 → List BSym) (a : BSym) :
    StackProg.applyAct (fun _ k => if k = 1 then .push a else .keep)
      (integerStore12 n negative tail frame) = integerStore12 n negative (a :: tail) frame := by
  funext k
  fin_cases k <;> rfl

private lemma integerPush_exec (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 7 → List BSym) (a : BSym) :
    (pushProg 1 a).Exec (integerStore12 n negative tail frame)
      (integerStore12 n negative (a :: tail) frame) 1 := by
  simpa only [pushProg, integerStore_push] using
    (StackProg.Exec.act (fun _ k => if k = 1 then .push a else .keep)
      (integerStore12 n negative tail frame))

private lemma integerSignTest_store (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 7 → List BSym) :
    integerSignTest (fun k => (integerStore12 n negative tail frame k).head?) =
      (negative && decide (0 < n)) := by
  cases negative <;> cases n <;> rfl

private lemma integerSign_exec (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 7 → List BSym) :
    (StackProg.branch integerSignTest (pushProg 1 .minus) integerKeep).Exec
      (integerStore12 n negative tail frame)
      (integerStore12 n negative
        ((if negative && decide (0 < n) then [BSym.minus] else []) ++ tail) frame) 2 := by
  by_cases h : (negative && decide (0 < n)) = true
  · have ht : integerSignTest (fun k => (integerStore12 n negative tail frame k).head?) = true := by
      rw [integerSignTest_store, h]
    have he := StackProg.Exec.branchTrue (q := integerKeep) ht
      (integerPush_exec n negative tail frame .minus)
    simpa [h] using he
  · have hf : (negative && decide (0 < n)) = false := Bool.eq_false_of_not_eq_true h
    have ht : integerSignTest (fun k => (integerStore12 n negative tail frame k).head?) = false := by
      rw [integerSignTest_store, hf]
    have hk : integerKeep.Exec (integerStore12 n negative tail frame)
        (integerStore12 n negative tail frame) 1 := by
      have hid : StackProg.applyAct (fun _ _ => StackAct.keep)
          (integerStore12 n negative tail frame) = integerStore12 n negative tail frame := by
        funext k
        rfl
      simpa only [integerKeep, hid] using
        (StackProg.Exec.act (fun _ _ => StackAct.keep) (integerStore12 n negative tail frame))
    have he := StackProg.Exec.branchFalse (p := pushProg 1 .minus) ht hk
    simpa [hf] using he

theorem integer_writer12 : ∃ (p : StackProg (Fin 12) BSym) (C : ℕ),
    ∀ (n : ℕ) (negative : Bool) (tail : List BSym) (frame : Fin 7 → List BSym), ∃ steps,
      p.Exec (integerStore12 n negative tail frame)
        (integerStore12 n negative
          (TensorNP.Eigen.encRat (if negative then -(n : ℚ) else (n : ℚ)) ++ tail) frame) steps ∧
      steps ≤ C * (n + 1)^2 := by
  obtain ⟨writer, C, hw⟩ := nativeWriter12
  refine ⟨integerProgram writer, C + 7, ?_⟩
  intro n negative tail frame
  obtain ⟨wt, heW, hwt⟩ := hw n (.one :: .sep :: tail) (integerFrame12 negative frame)
  have heW' : writer.Exec (integerStore12 n negative (.one :: .sep :: tail) frame)
      (integerStore12 n negative (encNat n ++ .one :: .sep :: tail) frame) wt := heW
  have he1 := integerPush_exec n negative tail frame .sep
  have he2 := integerPush_exec n negative (.sep :: tail) frame .one
  have he3 := integerSign_exec n negative (encNat n ++ .one :: .sep :: tail) frame
  have he := StackProg.Exec.seq he1 (StackProg.Exec.seq he2 (StackProg.Exec.seq heW' he3))
  have hone : encNat 1 = [BSym.one, BSym.sep] := by decide
  refine ⟨1 + 1 + (1 + 1 + (wt + 1 + 2)), ?_, ?_⟩
  · simpa only [integerProgram, integer_encoding, hone, List.append_assoc, List.cons_append, List.nil_append] using he
  · have hq : 1 ≤ (n + 1)^2 := Nat.one_le_pow 2 (n + 1) (by omega)
    nlinarith

end TensorNP.Encoder
end


/- Inlined module: IntegerWriter32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def integerPorts32 : Fin 12 ↪ Fin 32 := ⟨![18, 5, 20, 21, 22, 1, 7, 14, 15, 16, 19, 17], by decide⟩

def integerDecode32 (l : Fin 32) : Option (Fin 12) :=
  if l = 18 then some 0 else if l = 5 then some 1 else if l = 20 then some 2
  else if l = 21 then some 3 else if l = 22 then some 4 else if l = 1 then some 5
  else if l = 7 then some 6 else if l = 14 then some 7 else if l = 15 then some 8
  else if l = 16 then some 9 else if l = 19 then some 10 else if l = 17 then some 11 else none

lemma integerDecode32_spec (l : Fin 32) (k : Fin 12) :
    integerDecode32 l = some k ↔ integerPorts32 k = l := by
  fin_cases l <;> fin_cases k <;> decide

def integerFrameStore32 (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 32 → List BSym) : Fin 32 → List BSym :=
  fun k => if k = 18 then List.replicate n .one else if k = 5 then tail
    else if k = 19 then [if negative then .one else .zero]
    else if k = 20 ∨ k = 21 ∨ k = 22 then [] else frame k

def integerNativeFrame32 (frame : Fin 32 → List BSym) : Fin 7 → List BSym :=
  fun k => frame (integerPorts32 ⟨k.val + 5, by omega⟩)

lemma integerFrameStore32_project (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 32 → List BSym) :
    StackProgPortLift.project integerPorts32 (integerFrameStore32 n negative tail frame) =
      integerStore12 n negative tail (integerNativeFrame32 frame) := by
  funext k
  fin_cases k <;> rfl

private lemma integer_write_at (t : Fin 12 → List BSym) (s : Fin 32 → List BSym) (k : Fin 12) :
    StackProgPortLift.write integerPorts32 t s (integerPorts32 k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := integerPorts32.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma integerFrameStore32_write (n : ℕ) (negative : Bool) (tail tail' : List BSym)
    (frame : Fin 32 → List BSym) :
    StackProgPortLift.write integerPorts32 (integerStore12 n negative tail' (integerNativeFrame32 frame))
      (integerFrameStore32 n negative tail frame) = integerFrameStore32 n negative tail' frame := by
  classical
  funext l
  by_cases hl : ∃ k, integerPorts32 k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [integer_write_at]
    exact (congrFun (integerFrameStore32_project n negative tail' frame) k).symm
  · have h18 : l ≠ 18 := by
      intro he
      apply hl
      exact ⟨0, he.symm⟩
    have h5 : l ≠ 5 := by
      intro he
      apply hl
      exact ⟨1, he.symm⟩
    have h19 : l ≠ 19 := by
      intro he
      apply hl
      exact ⟨10, he.symm⟩
    have h20 : l ≠ 20 := by
      intro he
      apply hl
      exact ⟨2, he.symm⟩
    have h21 : l ≠ 21 := by
      intro he
      apply hl
      exact ⟨3, he.symm⟩
    have h22 : l ≠ 22 := by
      intro he
      apply hl
      exact ⟨4, he.symm⟩
    simp [StackProgPortLift.write, hl, integerFrameStore32, h18, h5, h19, h20, h21, h22]

theorem integer_writer32 : ∃ (p : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ (n : ℕ) (negative : Bool) (tail : List BSym) (frame : Fin 32 → List BSym), ∃ steps,
      p.Exec (integerFrameStore32 n negative tail frame)
        (integerFrameStore32 n negative
          (TensorNP.Eigen.encRat (if negative then -(n : ℚ) else (n : ℚ)) ++ tail) frame) steps ∧
      steps ≤ C * (n + 1)^2 := by
  obtain ⟨p, C, hp⟩ := integer_writer12
  refine ⟨StackProgPortLift.liftProgC integerPorts32 integerDecode32 p, C, ?_⟩
  intro n negative tail frame
  obtain ⟨steps, he, hb⟩ := hp n negative tail (integerNativeFrame32 frame)
  refine ⟨steps, ?_, hb⟩
  have he' := StackProgPortLift.liftProgC_exec integerPorts32 integerDecode32
    integerDecode32_spec he (integerFrameStore32 n negative tail frame)
    (integerFrameStore32_project n negative tail frame)
  rw [integerFrameStore32_write] at he'
  exact he'

end TensorNP.Encoder
end


/- Inlined module: SignedWriter32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def countWriterStore32 (x y : ℕ) (tail : List BSym) (frame : Fin 32 → List BSym) : Fin 32 → List BSym :=
  fun k => if k = 23 then List.replicate x .one else if k = 24 then List.replicate y .one
    else if k = 5 then tail else if k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨
      k = 25 ∨ k = 26 then [] else frame k

private lemma compare_start (x y : ℕ) (tail : List BSym) (frame : Fin 32 → List BSym) :
    compareFrameStore32 x y 0 0 [] (countWriterStore32 x y tail frame) = countWriterStore32 x y tail frame := by
  funext k
  fin_cases k <;> rfl

private lemma compare_to_integer (x y : ℕ) (tail : List BSym) (frame : Fin 32 → List BSym) :
    compareFrameStore32 x y (magnitude x y) 0 [if x < y then .one else .zero]
        (countWriterStore32 x y tail frame) =
      integerFrameStore32 (magnitude x y) (decide (x < y)) tail (countWriterStore32 x y tail frame) := by
  funext k
  fin_cases k <;> simp [compareFrameStore32, integerFrameStore32, countWriterStore32]

private def signedCleanup : StackProg (Fin 32) BSym :=
  .seq (clearProg 18) (.seq (clearProg 19) (.seq (clearProg 23) (clearProg 24)))

private lemma signedCleanup_exec (x y n : ℕ) (negative : Bool) (tail oldTail : List BSym)
    (frame : Fin 32 → List BSym) :
    signedCleanup.Exec (integerFrameStore32 n negative tail (countWriterStore32 x y oldTail frame))
      (countWriterStore32 0 0 tail frame) (3 * n + 3 * x + 3 * y + 10) := by
  let s0 := integerFrameStore32 n negative tail (countWriterStore32 x y oldTail frame)
  let s1 := Function.update s0 18 []
  let s2 := Function.update s1 19 []
  let s3 := Function.update s2 23 []
  let s4 := Function.update s3 24 []
  have he1 : (clearProg 18).Exec s0 s1 (3 * n + 1) := by
    simpa [s0, s1, integerFrameStore32] using (stack_basic_macros (18 : Fin 32) s0).2.2
  have he2 : (clearProg 19).Exec s1 s2 4 := by
    simpa [s0, s1, s2, integerFrameStore32] using (stack_basic_macros (19 : Fin 32) s1).2.2
  have he3 : (clearProg 23).Exec s2 s3 (3 * x + 1) := by
    simpa [s0, s1, s2, s3, integerFrameStore32, countWriterStore32] using
      (stack_basic_macros (23 : Fin 32) s2).2.2
  have he4 : (clearProg 24).Exec s3 s4 (3 * y + 1) := by
    simpa [s0, s1, s2, s3, s4, integerFrameStore32, countWriterStore32] using
      (stack_basic_macros (24 : Fin 32) s3).2.2
  have hend : s4 = countWriterStore32 0 0 tail frame := by
    funext k
    fin_cases k <;> simp [s0, s1, s2, s3, s4, integerFrameStore32, countWriterStore32, Function.update]
  rw [hend] at he4
  have he := StackProg.Exec.seq he1 (StackProg.Exec.seq he2 (StackProg.Exec.seq he3 he4))
  convert he using 1 <;> first | rfl | omega

theorem signed_count_writer32 : ∃ (p : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ (x y : ℕ) (tail : List BSym) (frame : Fin 32 → List BSym), ∃ steps,
      p.Exec (countWriterStore32 x y tail frame)
        (countWriterStore32 0 0 (TensorNP.Eigen.encRat ((x : ℚ) - (y : ℚ)) ++ tail) frame) steps ∧
      steps ≤ C * (x + y + 2)^2 := by
  obtain ⟨mag, hm⟩ := magnitude32
  obtain ⟨writer, C, hw⟩ := integer_writer32
  refine ⟨.seq mag (.seq writer signedCleanup), C + 100, ?_⟩
  intro x y tail frame
  let base := countWriterStore32 x y tail frame
  obtain ⟨mt, heM, hmt⟩ := hm x y base
  have heM' : mag.Exec (countWriterStore32 x y tail frame)
      (integerFrameStore32 (magnitude x y) (decide (x < y)) tail base) mt := by
    simpa only [base, compare_start, compare_to_integer] using heM
  obtain ⟨wt, heW, hwt⟩ := hw (magnitude x y) (decide (x < y)) tail base
  have hvalue : (if decide (x < y) then -(magnitude x y : ℚ) else (magnitude x y : ℚ)) =
      (x : ℚ) - (y : ℚ) := by
    simpa using magnitude_value x y
  rw [hvalue] at heW
  have heClean := signedCleanup_exec x y (magnitude x y) (decide (x < y))
    (TensorNP.Eigen.encRat ((x : ℚ) - (y : ℚ)) ++ tail) tail frame
  have he := StackProg.Exec.seq heM' (StackProg.Exec.seq heW heClean)
  refine ⟨_, he, ?_⟩
  have hmag := magnitude_le x y
  have hsquare : x + y + 2 ≤ (x + y + 2)^2 := Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) _
  have hwt' : wt ≤ C * (x + y + 2)^2 :=
    hwt.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) 2))
  have hsum : mt + 1 + (wt + 1 + (3 * magnitude x y + 3 * x + 3 * y + 10)) ≤
      C * (x + y + 2)^2 + 100 * (x + y + 2)^2 := by omega
  calc
    _ ≤ C * (x + y + 2)^2 + 100 * (x + y + 2)^2 := hsum
    _ = _ := by ring

end TensorNP.Encoder
end


/- Inlined module: OutputLanguage -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder

namespace TensorNP.BilinearEncoder

/-- Reset the signed coefficient counters after emitting one rational entry. -/
def resetCounts (R : RegFile) : RegFile :=
  Function.update (Function.update R 14 0) 15 0

/-- Finite register code extended by the checked signed-rational writer. -/
inductive OutputCmd where
  | reg (p : RegCmd)
  | emit
  | seq (p q : OutputCmd)
  | branch (less : Bool) (r s : Fin 21) (yes no : OutputCmd)
  | down (r : Fin 21) (body : OutputCmd)

/-- The output is explicit in the state; all register work preserves its tail. -/
inductive OutputExec (C : ℕ) (data : List BSym) :
    OutputCmd → RegFile → List BSym → RegFile → List BSym → ℕ → Prop where
  | reg {p R T n} (out) : RegExec data p R T n →
      OutputExec C data (.reg p) R out T out n
  | emit (R out) : OutputExec C data .emit R out (resetCounts R)
      (TensorNP.Eigen.encRat ((R 14 : ℚ) - (R 15 : ℚ)) ++ out)
      (C * (R 14 + R 15 + 2)^2)
  | seq {p q R S T x y z n m} :
      OutputExec C data p R x S y n → OutputExec C data q S y T z m →
      OutputExec C data (.seq p q) R x T z (n + 1 + m)
  | branch {less r s yes no R T x y n} :
      OutputExec C data (if regCompare less r s R then yes else no) R x T y n →
      OutputExec C data (.branch less r s yes no) R x T y (regCharge R + n)
  | downFalse {r body R out} : R r = 0 →
      OutputExec C data (.down r body) R out R out 1
  | downTrue {r body R S T x y z n m} : 0 < R r →
      OutputExec C data body (Function.update R r (R r - 1)) x S y n →
      OutputExec C data (.down r body) S y T z m →
      OutputExec C data (.down r body) R x T z (n + m + 5)

/-- Compilation uses only the published finite-stack programs and guards. -/
noncomputable def compileOutput (writer : StackProg (Fin 32) BSym) :
    OutputCmd → StackProg (Fin 32) BSym
  | .reg p => compileReg actualRegBackend p
  | .emit => writer
  | .seq p q => .seq (compileOutput writer p) (compileOutput writer q)
  | .branch less r s yes no =>
      actualRegBackend.branch less r s (compileOutput writer yes) (compileOutput writer no)
  | .down r body => .loop (fun h => (h (regPorts r)).isSome)
      (.seq (popProg (regPorts r)) (compileOutput writer body))

end TensorNP.BilinearEncoder
end


/- Inlined module: MatrixLoops -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

/-- The matrix loop owns only row and column registers 12 and 13. -/
def cellState (R : RegFile) (row col : ℕ) : RegFile :=
  Function.update (Function.update R 12 row) 13 col

def columnChunk (E : ℕ → ℕ → List BSym) (row count : ℕ) : List BSym :=
  (List.range count).flatMap (E row)

def matrixChunk (E : ℕ → ℕ → List BSym) (N count : ℕ) : List BSym :=
  (List.range count).flatMap (fun row => columnChunk E row N)

def columnLoop (entry : OutputCmd) : OutputCmd := .down 13 entry
def rowLoop (entry : OutputCmd) : OutputCmd :=
  .down 12 (.seq (.reg (.assign 13 6)) (columnLoop entry))

def MatrixEntrySpec (C : ℕ) (data : List BSym) (entry : OutputCmd)
    (E : ℕ → ℕ → List BSym) (R : RegFile) (N B : ℕ) : Prop :=
  ∀ (row col : ℕ) (tail : List BSym), row < N → col < N →
    ∃ steps, OutputExec C data entry (cellState R row col) tail
      (cellState R row col) (E row col ++ tail) steps ∧ steps ≤ B

-- Register framing identities for the two matrix-loop counters.
lemma cellState_down_row (R : RegFile) (row : ℕ) :
    Function.update (cellState R (row + 1) 0) 12
      (cellState R (row + 1) 0 12 - 1) = cellState R row 0 := by
  funext r
  by_cases h12 : r = 12 <;> by_cases h13 : r = 13 <;> simp [cellState, h12, h13]

lemma cellState_assign_col (R : RegFile) (row N : ℕ) (hN : R 6 = N) :
    Function.update (cellState R row 0) 13 (cellState R row 0 6) =
      cellState R row N := by
  funext r
  by_cases h12 : r = 12 <;> by_cases h13 : r = 13 <;> simp [cellState, h12, h13, hN]

theorem columnLoop_exec (C : ℕ) (data : List BSym) (entry : OutputCmd)
    (E : ℕ → ℕ → List BSym) (R : RegFile) (N B : ℕ)
    (hentry : MatrixEntrySpec C data entry E R N B) (row count : ℕ)
    (hr : row < N) (hc : count ≤ N) (tail : List BSym) :
    ∃ steps, OutputExec C data (columnLoop entry) (cellState R row count) tail
      (cellState R row 0) (columnChunk E row count ++ tail) steps ∧
      steps ≤ count * (B + 5) + 1 := by
  induction count generalizing tail with
  | zero =>
    refine ⟨1, ?_, by simp⟩
    simpa [columnLoop, columnChunk] using
      (OutputExec.downFalse (C := C) (data := data) (r := 13) (body := entry)
        (R := cellState R row 0) (out := tail) (by simp [cellState]))
  | succ count ih =>
    obtain ⟨u, hu, hub⟩ := hentry row count tail hr (by omega)
    obtain ⟨v, hv, hvb⟩ := ih (by omega) (E row count ++ tail)
    have hpop : Function.update (cellState R row (count+1)) 13
        (cellState R row (count+1) 13-1) = cellState R row count := by
      funext r
      by_cases h13 : r = 13 <;> simp [cellState, h13]
    have hbody : OutputExec C data entry
        (Function.update (cellState R row (count+1)) 13
          (cellState R row (count+1) 13-1)) tail
        (cellState R row count) (E row count ++ tail) u := by
      rw [hpop]
      exact hu
    have he := OutputExec.downTrue (r := 13) (R := cellState R row (count+1))
      (by simp [cellState]) hbody hv
    refine ⟨u+v+5, ?_, ?_⟩
    · simpa [columnLoop, columnChunk, List.range_succ, List.flatMap_append,
        List.append_assoc] using he
    · rw [Nat.add_mul, Nat.one_mul]
      omega

/-- Reverse counter traversal plus prepending produces ascending row-major order. -/
theorem rowLoop_exec (C : ℕ) (data : List BSym) (entry : OutputCmd)
    (E : ℕ → ℕ → List BSym) (R : RegFile) (N B Q : ℕ)
    (hN : R 6 = N) (hentry : MatrixEntrySpec C data entry E R N B)
    (hQ : ∀ row, row < N → regCharge (cellState R row 0) ≤ Q)
    (count : ℕ) (hc : count ≤ N) (tail : List BSym) :
    ∃ steps, OutputExec C data (rowLoop entry) (cellState R count 0) tail
      (cellState R 0 0) (matrixChunk E N count ++ tail) steps ∧
      steps ≤ count * (Q + N * (B + 5) + 7) + 1 := by
  induction count generalizing tail with
  | zero =>
    refine ⟨1, ?_, by simp⟩
    simpa [rowLoop, matrixChunk] using
      (OutputExec.downFalse (C := C) (data := data) (r := 12)
        (body := .seq (.reg (.assign 13 6)) (columnLoop entry))
        (R := cellState R 0 0) (out := tail) (by simp [cellState]))
  | succ count ih =>
    obtain ⟨u, hu, hub⟩ := columnLoop_exec C data entry E R N B hentry count N
      (by omega) le_rfl tail
    obtain ⟨v, hv, hvb⟩ := ih (by omega) (columnChunk E count N ++ tail)
    have ha : OutputExec C data (.reg (.assign 13 6)) (cellState R count 0) tail
        (cellState R count N) tail (regCharge (cellState R count 0)) := by
      simpa only [cellState_assign_col R count N hN] using
        (OutputExec.reg (C := C) tail
          (RegExec.assign (data := data) (cellState R count 0) 13 6))
    have hbody : OutputExec C data (.seq (.reg (.assign 13 6)) (columnLoop entry))
        (Function.update (cellState R (count + 1) 0) 12
          (cellState R (count + 1) 0 12 - 1)) tail
        (cellState R count 0) (columnChunk E count N ++ tail)
        (regCharge (cellState R count 0) + 1 + u) := by
      simpa only [cellState_down_row] using (OutputExec.seq ha hu)
    have he := OutputExec.downTrue (r := 12) (R := cellState R (count + 1) 0)
      (by simp [cellState]) hbody hv
    refine ⟨regCharge (cellState R count 0) + 1 + u + v + 5, ?_, ?_⟩
    · simpa [rowLoop, matrixChunk, List.range_succ, List.flatMap_append,
        List.append_assoc] using he
    · have hcharge := hQ count (by omega)
      rw [Nat.add_mul, Nat.one_mul]
      omega

end TensorNP.BilinearEncoder
end


/- Inlined module: RawPayload -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def minorValue (a b row col : ℕ) : ℚ :=
  (naturalMonomial a b row col : ℚ) - (naturalMonomial b a row col : ℚ)

def colorValue (v : ℕ) (data : List BSym) (family vertex row col : ℕ) : ℚ :=
  (rawPositiveCount v data family vertex row col : ℚ) -
    (rawNegativeCount v family vertex row col : ℚ)

/-- The four signed blocks of the published bilinear realification. -/
def realEntryValue (high : Bool) (N : ℕ) (A : ℕ → ℕ → ℚ) (row col : ℕ) : ℚ :=
  if row < N then
    if col < N then (if high then 0 else A row col)
    else (if high then A row (col - N) else 0)
  else
    if col < N then (if high then A (row - N) col else 0)
    else (if high then 0 else -A (row - N) (col - N))

def matrixValueWord (A : ℕ → ℕ → ℚ) (N : ℕ) : List BSym :=
  matrixChunk (fun row col => TensorNP.Eigen.encRat (A row col)) N N

/-- `none` emits the complex tensor; `some high` emits one doubled slice block. -/
def sliceValueWord (mode : Option Bool) (N : ℕ) (A : ℕ → ℕ → ℚ) : List BSym :=
  match mode with
  | none => matrixValueWord A N
  | some high => matrixValueWord (realEntryValue high N A) (N + N)

/-- Direct row-major candidates followed by the four color families. -/
def passWord (mode : Option Bool) (v : ℕ) (data : List BSym) : List BSym :=
  let N := 2 * v + 1
  ((List.range N).flatMap fun a => (List.range N).flatMap fun b =>
    if a < b then sliceValueWord mode N (minorValue a b) else []) ++
    ((List.range 4).flatMap fun family => (List.range v).flatMap fun vertex =>
      sliceValueWord mode N (colorValue v data family vertex))

/-- The zero graph uses one feasible zero slice instead of the empty AG slice set. -/
def complexPayload (v : ℕ) (data : List BSym) : List BSym :=
  if v = 0 then
    encNats [1, 1, 1] ++ matrixValueWord (minorValue 0 0) 1
  else
    encNats [v * (2 * v + 5), 2 * v + 1, 2 * v + 1] ++ passWord none v data

/-- The low slice block precedes the high block in the published tensor code. -/
def realPayload (v : ℕ) (data : List BSym) : List BSym :=
  if v = 0 then
    encNats [2, 2, 2] ++
      (matrixValueWord (minorValue 0 0) 2 ++ matrixValueWord (minorValue 0 0) 2)
  else
    let L := v * (2 * v + 5)
    let N := 2 * v + 1
    encNats [L + L, N + N, N + N] ++
      (passWord (some false) v data ++ passWord (some true) v data)

end TensorNP.BilinearEncoder
end


/- Inlined module: WordMatrix -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

theorem matrixValueWord_eq_ofFn {N : ℕ} (A : ℕ → ℕ → ℚ) (B : Fin N → Fin N → ℚ)
    (h : ∀ i j, A i.val j.val = B i j) :
    matrixValueWord A N =
      (List.ofFn (fun i : Fin N => (List.ofFn (fun j : Fin N =>
        TensorNP.Eigen.encRat (B i j))).flatten)).flatten := by
  unfold matrixValueWord matrixChunk
  apply rangeFlatMap_ofFn
  intro i
  unfold columnChunk
  apply rangeFlatMap_ofFn
  intro j
  exact congrArg TensorNP.Eigen.encRat (h i j)

theorem squareWord_eq_ofFn (N : ℕ) (E : ℕ → ℕ → List BSym) :
    (List.range N).flatMap (fun a => (List.range N).flatMap (fun b => E a b)) =
      (List.ofFn (fun q : Fin (N * N) =>
        E (finProdFinEquiv.symm q).1.val (finProdFinEquiv.symm q).2.val)).flatten := by
  rw [List.ofFn_mul']
  rw [List.flatten_flatten]
  simp only [List.map_ofFn]
  apply rangeFlatMap_ofFn
  intro i
  apply rangeFlatMap_ofFn
  intro j
  have heq : (⟨N * i.val + j.val, by nlinarith [Nat.mul_le_mul_left N i.isLt, j.isLt]⟩ : Fin (N * N)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm]
  rw [heq, Equiv.symm_apply_apply]

end TensorNP.BilinearEncoder
end


/- Inlined module: EntryBridge -/
section
set_option autoImplicit false
open TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def colorSlice {v : ℕ} (f : Fin 4) (i : Fin v) : Bilinear.SliceIdx v :=
  if h : f.val < 3 then .inr (.inl (⟨f.val, h⟩, i)) else .inr (.inr i)

theorem monomialEntry_unit {N : ℕ} (a b p q : Fin N) :
    monomialEntry a.val b.val p.val q.val = Bilinear.unitMat a b p q := by
  simp [monomialEntry, Bilinear.unitMat, Fin.ext_iff, eq_comm]

theorem colorEntryInt_AG {v : ℕ} (G : SimpleGraph (Fin v))
    (f : Fin 4) (i : Fin v) (p q : Fin (2 * v + 1)) :
    colorEntryInt G (f, i) p q = Bilinear.AG G (colorSlice f i) p q := by
  classical
  fin_cases f <;> simp [colorEntryInt, colorSlice, Bilinear.AG, Bilinear.unitMat,
    monomialEntry, Bilinear.xIdx, Bilinear.yIdx, Bilinear.zIdx, Fin.ext_iff, eq_comm]

theorem rawColorEntry_AG {v : ℕ} (G : SimpleGraph (Fin v))
    (f : Fin 4) (i : Fin v) (p q : Fin (2 * v + 1)) :
    rawColorEntry v (graphData G) f.val i.val p.val q.val =
      Bilinear.AG G (colorSlice f i) p q := by
  exact (rawColorEntry_graphData G (f, i) p q).trans (colorEntryInt_AG G f i p q)

theorem minorCounts_value {N : ℕ} (ab : Bilinear.MinorIdx N) (p q : Fin N) :
    ((naturalMonomial ab.val.1.val ab.val.2.val p.val q.val : ℕ) : ℤ) -
      ((naturalMonomial ab.val.2.val ab.val.1.val p.val q.val : ℕ) : ℤ) =
      Bilinear.minorSlice ab p q := by
  simp [naturalMonomial_cast, monomialEntry, Bilinear.minorSlice, Fin.ext_iff, eq_comm]

end TensorNP.BilinearEncoder
end


/- Inlined module: BoundedMatrix -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

/-- A finite matrix extended by zero outside its two dimensions. -/
def boundedValue {N : ℕ} (A : Fin N → Fin N → ℚ) (row col : ℕ) : ℚ :=
  if hr : row < N then if hc : col < N then A ⟨row, hr⟩ ⟨col, hc⟩ else 0 else 0

@[simp] theorem boundedValue_fin {N : ℕ} (A : Fin N → Fin N → ℚ) (p q : Fin N) :
    boundedValue A p.val q.val = A p q := by
  simp [boundedValue]

def finiteMatrixWord {N : ℕ} (A : Fin N → Fin N → ℚ) : List BSym :=
  (List.ofFn fun p => (List.ofFn fun q => TensorNP.Eigen.encRat (A p q)).flatten).flatten

end TensorNP.BilinearEncoder
end


/- Inlined module: WordCongr -/
section
set_option autoImplicit false
namespace TensorNP.BilinearEncoder

theorem matrixValueWord_congr {N : ℕ} (A B : ℕ → ℕ → ℚ)
    (h : ∀ row col, row < N → col < N → A row col = B row col) :
    matrixValueWord A N = matrixValueWord B N := by
  calc
    matrixValueWord A N = (List.ofFn (fun i : Fin N => (List.ofFn (fun j : Fin N =>
        TensorNP.Eigen.encRat (B i.val j.val))).flatten)).flatten :=
      matrixValueWord_eq_ofFn A (fun i j => B i.val j.val) (fun i j => h i.val j.val i.isLt j.isLt)
    _ = matrixValueWord B N :=
      (matrixValueWord_eq_ofFn B (fun i j => B i.val j.val) (fun _ _ => rfl)).symm

theorem realEntryValue_congr (high : Bool) {N : ℕ} (A B : ℕ → ℕ → ℚ)
    (h : ∀ row col, row < N → col < N → A row col = B row col)
    (row col : ℕ) (hrow : row < N+N) (hcol : col < N+N) :
    realEntryValue high N A row col = realEntryValue high N B row col := by
  have hr' : row - N < N := by omega
  have hc' : col - N < N := by omega
  cases high <;> by_cases hr : row < N <;> by_cases hc : col < N <;>
    simp only [realEntryValue, hr, hc, Bool.false_eq_true, ↓reduceIte] <;>
    first | rfl | exact h row col hr hc | exact h row (col-N) hr hc' |
      exact h (row-N) col hr' hc | exact congrArg (fun x : ℚ => -x) (h (row-N) (col-N) hr' hc')

theorem sliceValueWord_congr (mode : Option Bool) (N : ℕ) (A B : ℕ → ℕ → ℚ)
    (h : ∀ row col, row < N → col < N → A row col = B row col) :
    sliceValueWord mode N A = sliceValueWord mode N B := by
  cases mode with
  | none => exact matrixValueWord_congr A B h
  | some high =>
      apply matrixValueWord_congr
      intro row col hrow hcol
      exact realEntryValue_congr high A B h row col hrow hcol

end TensorNP.BilinearEncoder
end


/- Inlined module: ValueAG -/
section
set_option autoImplicit false
open TensorNP.Encoder
namespace TensorNP.BilinearEncoder

theorem minorValue_AG {N : ℕ} (ab : Bilinear.MinorIdx N) (p q : Fin N) :
    minorValue ab.val.1.val ab.val.2.val p.val q.val = (Bilinear.minorSlice ab p q : ℚ) := by
  have h := congrArg (fun z : ℤ => (z : ℚ)) (minorCounts_value ab p q)
  simpa only [minorValue, Int.cast_sub, Int.cast_natCast] using h

theorem colorValue_AG {v : ℕ} (G : SimpleGraph (Fin v)) (f : Fin 4) (i : Fin v)
    (p q : Fin (2*v+1)) :
    colorValue v (graphData G) f.val i.val p.val q.val = (Bilinear.AG G (colorSlice f i) p q : ℚ) := by
  have h := congrArg (fun z : ℤ => (z : ℚ)) (rawColorEntry_AG G f i p q)
  simpa only [colorValue, rawColorEntry, Int.cast_sub, Int.cast_natCast] using h

end TensorNP.BilinearEncoder
end


/- Inlined module: ZeroPayload -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity
namespace TensorNP.BilinearEncoder

theorem complex_payload_code_zero (data : List BSym) (G : SimpleGraph (Fin 0)) :
    complexPayload 0 data = Bilinear.tensorCode (complexTensor G) := by
  simp [complexPayload, Bilinear.tensorCode, complexTensor, complexSlices, matrixValueWord,
    matrixChunk, columnChunk, minorValue, List.ofFn_succ, List.range_succ]

lemma realTensor_zero (G : SimpleGraph (Fin 0)) (s p q : Fin 2) :
    realTensor G s p q = 0 := by
  fin_cases s <;> fin_cases p <;> fin_cases q <;> rfl

theorem real_payload_code_zero (data : List BSym) (G : SimpleGraph (Fin 0)) :
    realPayload 0 data = Bilinear.tensorCode (realTensor G) := by
  simp [realPayload, Bilinear.tensorCode, complexSlices, realTensor_zero, matrixValueWord,
    matrixChunk, columnChunk, minorValue, List.ofFn_succ, List.range_succ, List.append_assoc]

end TensorNP.BilinearEncoder
end


/- Inlined module: RealWord -/
section
set_option autoImplicit false
set_option maxHeartbeats 100000
open ProjSchedTW.Complexity TensorNP.Encoder TensorNP.Bilinear
namespace TensorNP.BilinearEncoder

theorem realEntryValue_sum {N : ℕ} (high : Bool) (A : Fin N → Fin N → ℚ)
    (p q : Fin N ⊕ Fin N) :
    realEntryValue high N (boundedValue A) (finSumFinEquiv p).val (finSumFinEquiv q).val =
      doubling (fun (_ : Unit) i j => A i j)
        (if high then Sum.inr () else Sum.inl ()) p q := by
  cases high <;> cases p <;> cases q <;>
    simp [realEntryValue, boundedValue, doubling]

theorem realEntryValue_fin {N : ℕ} (high : Bool) (A : Fin N → Fin N → ℚ)
    (p q : Fin (N+N)) :
    realEntryValue high N (boundedValue A) p.val q.val =
      doubling (fun (_ : Unit) i j => A i j)
        (if high then Sum.inr () else Sum.inl ())
        (finSumFinEquiv.symm p) (finSumFinEquiv.symm q) := by
  simpa only [Equiv.apply_symm_apply] using
    realEntryValue_sum high A (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)

theorem realSliceValueWord {N : ℕ} (high : Bool) (A : Fin N → Fin N → ℚ) :
    sliceValueWord (some high) N (boundedValue A) =
      finiteMatrixWord (fun p q => doubling (fun (_ : Unit) i j => A i j)
        (if high then Sum.inr () else Sum.inl ())
        (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)) := by
  exact matrixValueWord_eq_ofFn _ _ (realEntryValue_fin high A)

theorem complexSliceValueWord {N : ℕ} (A : Fin N → Fin N → ℚ) :
    sliceValueWord none N (boundedValue A) = finiteMatrixWord A := by
  exact matrixValueWord_eq_ofFn _ _ (boundedValue_fin A)

private theorem realWord_sumSymm_castLE {m n : ℕ} (i : Fin m) :
    finSumFinEquiv.symm (Fin.castLE (Nat.le_add_right m n) i) = Sum.inl i := by
  simpa [Fin.castAdd] using (finSumFinEquiv_symm_apply_castAdd (n := n) i)

theorem sumWord_split {m n : ℕ} (W : Fin m ⊕ Fin n → List BSym) :
    (List.ofFn (fun s : Fin (m+n) => W (finSumFinEquiv.symm s))).flatten =
      (List.ofFn (fun s : Fin m => W (Sum.inl s))).flatten ++
      (List.ofFn (fun s : Fin n => W (Sum.inr s))).flatten := by
  simp [List.ofFn_add, realWord_sumSymm_castLE]

theorem doubling_slice {I J K R : Type*} [Ring R] (A : I → J → K → R)
    (i : I) (high : Bool) (p : J ⊕ J) (q : K ⊕ K) :
    doubling (fun (_ : Unit) j k => A i j k)
      (if high then Sum.inr () else Sum.inl ()) p q =
      doubling A (if high then Sum.inr i else Sum.inl i) p q := by
  cases high <;> cases p <;> cases q <;> rfl

theorem realSliceValueWord_of_tensor {I : Type*} {N : ℕ}
    (A : I → Fin N → Fin N → ℚ) (i : I) (high : Bool) :
    sliceValueWord (some high) N (boundedValue (A i)) =
      finiteMatrixWord (fun p q => doubling A
        (if high then Sum.inr i else Sum.inl i)
        (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)) := by
  simpa only [doubling_slice] using realSliceValueWord high (A i)

theorem doubling_tensorCode {L N : ℕ} (A : Fin L → Fin N → Fin N → ℚ) :
    tensorCode (fun s p q => doubling A (finSumFinEquiv.symm s)
      (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)) =
      encNats [L+L, N+N, N+N] ++
        ((List.ofFn (fun s : Fin L => sliceValueWord (some false) N
          (boundedValue (A s)))).flatten ++
         (List.ofFn (fun s : Fin L => sliceValueWord (some true) N
          (boundedValue (A s)))).flatten) := by
  change encNats [L+L, N+N, N+N] ++
    (List.ofFn (fun s => finiteMatrixWord (fun p q => doubling A (finSumFinEquiv.symm s)
      (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)))).flatten = _
  rw [sumWord_split (fun s : Fin L ⊕ Fin L => finiteMatrixWord
    (fun p q => doubling A s (finSumFinEquiv.symm p) (finSumFinEquiv.symm q)))]
  simp only [realSliceValueWord_of_tensor, Bool.false_eq_true, ↓reduceIte]

end TensorNP.BilinearEncoder
end


/- Inlined module: PayloadCode -/
section
namespace TensorNP.BilinearEncoder.PayloadProof

-- Audited source body: CandidateWord

set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Bilinear

def minorCandidates (N : ℕ) : List (Fin N × Fin N) :=
  List.ofFn (finProdFinEquiv.symm : Fin (N*N) → Fin N × Fin N)

def chooseMinor (N : ℕ) (ab : Fin N × Fin N) : Option (MinorIdx N) :=
  if h : ab.1 < ab.2 then some ⟨ab,h⟩ else none

private def selectedMinors (N : ℕ) : List (MinorIdx N) :=
  (minorCandidates N).filterMap (chooseMinor N)

private theorem selected_values (N : ℕ) (xs : List (Fin N × Fin N)) :
    (xs.filterMap (chooseMinor N)).map Subtype.val = xs.filter (fun ab ↦ decide (ab.1 < ab.2)) := by
  induction xs with
  | nil => rfl
  | cons ab xs ih =>
      by_cases h : ab.1 < ab.2 <;> simp [chooseMinor, h, ih]

private theorem selected_eq_enumeration (N count : ℕ) (e : Fin count ≃ MinorIdx N)
    (he : List.ofFn (fun k : Fin count ↦ (e k).val) =
      (minorCandidates N).filter (fun ab ↦ decide (ab.1 < ab.2))) :
    selectedMinors N = List.ofFn e := by
  apply (List.map_injective_iff.mpr Subtype.coe_injective)
  rw [selectedMinors, selected_values]
  simpa [List.map_ofFn, Function.comp_def] using he.symm

private theorem flatten_candidates {α : Type*} (N : ℕ) (xs : List (Fin N × Fin N))
    (word : MinorIdx N → List α) :
    (xs.map (fun ab ↦ (chooseMinor N ab).elim [] word)).flatten =
      ((xs.filterMap (chooseMinor N)).map word).flatten := by
  induction xs with
  | nil => rfl
  | cons ab xs ih =>
      cases h : chooseMinor N ab <;> simp [h, ih]

private theorem candidate_words_eq {α : Type*} (N count : ℕ) (e : Fin count ≃ MinorIdx N)
    (he : List.ofFn (fun k : Fin count ↦ (e k).val) =
      (minorCandidates N).filter (fun ab ↦ decide (ab.1 < ab.2)))
    (word : MinorIdx N → List α) :
    ((minorCandidates N).map (fun ab ↦ (chooseMinor N ab).elim [] word)).flatten =
      ((List.ofFn e).map word).flatten := by
  rw [flatten_candidates]
  change ((selectedMinors N).map word).flatten = _
  rw [selected_eq_enumeration N count e he]

theorem minorCandidate_word_eq (N : ℕ) (W : ℕ → ℕ → List BSym)
    (word : MinorIdx N → List BSym)
    (hword : ∀ ab, W ab.val.1.val ab.val.2.val = word ab) :
    (List.range N).flatMap (fun a => (List.range N).flatMap (fun b =>
      if a < b then W a b else [])) =
      (List.ofFn (fun i : Fin (N.choose 2) => word (minorEquiv N i))).flatten := by
  rw [squareWord_eq_ofFn]
  have hgrid : (List.ofFn (fun q : Fin (N*N) =>
      if (finProdFinEquiv.symm q).1.val < (finProdFinEquiv.symm q).2.val then
        W (finProdFinEquiv.symm q).1.val (finProdFinEquiv.symm q).2.val else [])).flatten =
      ((minorCandidates N).map (fun ab => (chooseMinor N ab).elim [] word)).flatten := by
    simp only [minorCandidates, List.map_ofFn, Function.comp_def]
    apply congrArg List.flatten
    congr 1
    funext q
    let ab := finProdFinEquiv.symm q
    change (if ab.1.val < ab.2.val then W ab.1.val ab.2.val else []) =
      (chooseMinor N ab).elim [] word
    by_cases h : ab.1 < ab.2
    · have hv : ab.1.val < ab.2.val := h
      simp only [chooseMinor, dif_pos h, if_pos hv, Option.elim_some]
      exact hword ⟨ab,h⟩
    · have hv : ¬ ab.1.val < ab.2.val := h
      simp only [chooseMinor, dif_neg h, if_neg hv, Option.elim_none]
  rw [hgrid]
  have he : List.ofFn (fun k : Fin (N.choose 2) => (minorEquiv N k).val) =
      (minorCandidates N).filter (fun ab => decide (ab.1 < ab.2)) := by
    simpa [minorPairs, minorCandidates] using minorEquiv_order N
  simpa only [List.map_ofFn, Function.comp_def] using
    (candidate_words_eq N (N.choose 2) (minorEquiv N) he word)



-- Audited source body: ColorWord

set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Encoder

theorem colorWord_eq_ofFn {v : ℕ} (W : ℕ → ℕ → List BSym)
    (word : Bilinear.SliceIdx v → List BSym)
    (h : ∀ (f : Fin 4) (i : Fin v), W f.val i.val = word (colorSlice f i)) :
    (List.range 4).flatMap (fun family => (List.range v).flatMap (W family)) =
      (List.ofFn (fun p : Fin (3 * v) =>
        word (Sum.inr (Sum.inl (finProdFinEquiv.symm p))))).flatten ++
      (List.ofFn (fun i : Fin v => word (Sum.inr (Sum.inr i)))).flatten := by
  rw [List.ofFn_mul]
  have hp (i : Fin 3) (j : Fin v) :
      finProdFinEquiv.symm (⟨i.val * v + j.val,
        by nlinarith [Nat.mul_le_mul_right v i.isLt, j.isLt]⟩ : Fin (3 * v)) = (i, j) := by
    have heq : (⟨i.val * v + j.val,
        by nlinarith [Nat.mul_le_mul_right v i.isLt, j.isLt]⟩ : Fin (3 * v)) =
        finProdFinEquiv (i, j) := by
      apply Fin.ext
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
    rw [heq, Equiv.symm_apply_apply]
  simp only [hp]
  have hr (f : Fin 4) : (List.range v).flatMap (W f.val) =
      (List.ofFn (fun i : Fin v => word (colorSlice f i))).flatten := by
    apply rangeFlatMap_ofFn
    intro i
    exact h f i
  have h0 := hr (0 : Fin 4)
  simp [colorSlice] at h0
  obtain ⟨h1, h2, h3⟩ := And.intro (hr (1 : Fin 4)) (And.intro (hr (2 : Fin 4)) (hr (3 : Fin 4)))
  simp [colorSlice] at h1 h2 h3
  simp [List.range_succ, List.ofFn_succ, h0, h1, h2, h3, List.append_assoc]



-- Audited source body: PassWord

set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Bilinear TensorNP.Encoder

noncomputable def agSliceWord {v : ℕ} (mode : Option Bool) (G : SimpleGraph (Fin v))
    (s : Bilinear.SliceIdx v) : List BSym :=
  sliceValueWord mode (2*v+1) (boundedValue (fun p q => (Bilinear.AG G s p q : ℚ)))

theorem passWord_eq_slices (mode : Option Bool) {v : ℕ} (G : SimpleGraph (Fin v)) :
    passWord mode v (graphData G) =
      (List.ofFn (fun s : Fin (v*(2*v+5)) => agSliceWord mode G (explicitSliceEquiv v s))).flatten := by
  have hminor : ∀ ab : Bilinear.MinorIdx (2*v+1),
      sliceValueWord mode (2*v+1) (minorValue ab.val.1.val ab.val.2.val) =
        agSliceWord mode G (Sum.inl ab) := by
    intro ab
    apply sliceValueWord_congr
    intro row col hr hc
    let p : Fin (2*v+1) := ⟨row, hr⟩
    let q : Fin (2*v+1) := ⟨col, hc⟩
    change minorValue ab.val.1.val ab.val.2.val p.val q.val =
      boundedValue (fun x y => (Bilinear.AG G (.inl ab) x y : ℚ)) p.val q.val
    rw [boundedValue_fin]
    exact minorValue_AG ab p q
  have hcolor : ∀ (f : Fin 4) (i : Fin v),
      sliceValueWord mode (2*v+1) (colorValue v (graphData G) f.val i.val) =
        agSliceWord mode G (colorSlice f i) := by
    intro f i
    apply sliceValueWord_congr
    intro row col hr hc
    let p : Fin (2*v+1) := ⟨row, hr⟩
    let q : Fin (2*v+1) := ⟨col, hc⟩
    change colorValue v (graphData G) f.val i.val p.val q.val =
      boundedValue (fun x y => (Bilinear.AG G (colorSlice f i) x y : ℚ)) p.val q.val
    rw [boundedValue_fin]
    exact colorValue_AG G f i p q
  have hm := minorCandidate_word_eq (2*v+1)
    (fun a b => sliceValueWord mode (2*v+1) (minorValue a b))
    (fun ab => agSliceWord mode G (Sum.inl ab)) hminor
  have hc := colorWord_eq_ofFn
    (fun f i => sliceValueWord mode (2*v+1) (colorValue v (graphData G) f i))
    (agSliceWord mode G) hcolor
  have ho := congrArg (fun xs : List (Bilinear.SliceIdx v) =>
    (xs.map (agSliceWord mode G)).flatten) (explicitSliceEquiv_order v)
  simp only [List.map_ofFn, List.map_append, List.flatten_append, Function.comp_def] at ho
  unfold passWord
  dsimp only
  rw [hm, hc]
  simpa only [List.append_assoc] using ho.symm



-- Audited source body: ComplexPayload

set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Encoder

theorem complex_payload_code {v : ℕ} (G : SimpleGraph (Fin v)) :
    complexPayload v (graphData G) = Bilinear.tensorCode (complexTensor G) := by
  cases v with
  | zero => exact complex_payload_code_zero _ G
  | succ v =>
    simp only [complexPayload, Nat.succ_ne_zero, if_false, Bilinear.tensorCode, complexTensor, complexSlices]
    rw [passWord_eq_slices]
    congr 1
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext s
    exact matrixValueWord_eq_ofFn _ _ (boundedValue_fin _)



-- Audited source body: RealPayload

set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Encoder

theorem real_payload_code {v : ℕ} (G : SimpleGraph (Fin v)) :
    realPayload v (graphData G) = Bilinear.tensorCode (realTensor G) := by
  cases v with
  | zero => exact real_payload_code_zero _ G
  | succ v =>
    change realPayload (v+1) (graphData G) = Bilinear.tensorCode
      (fun s p q => Bilinear.doubling (complexTensor G) (finSumFinEquiv.symm s)
        (finSumFinEquiv.symm p) (finSumFinEquiv.symm q))
    rw [doubling_tensorCode]
    simp only [realPayload, Nat.succ_ne_zero, if_false, passWord_eq_slices,
      agSliceWord, complexSlices, complexTensor]


end TensorNP.BilinearEncoder.PayloadProof

namespace TensorNP.BilinearEncoder

theorem complex_payload_code {v : ℕ} (G : SimpleGraph (Fin v)) :
    complexPayload v (TensorNP.Encoder.graphData G) = Bilinear.tensorCode (complexTensor G) :=
  PayloadProof.complex_payload_code G

theorem real_payload_code {v : ℕ} (G : SimpleGraph (Fin v)) :
    realPayload v (TensorNP.Encoder.graphData G) = Bilinear.tensorCode (realTensor G) :=
  PayloadProof.real_payload_code G

end TensorNP.BilinearEncoder
end


/- Inlined module: OutputCore -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder

namespace TensorNP.BilinearEncoder

/-- A register state with an explicit output word; the graph table stays in port 7. -/
noncomputable def outputStore (frame : Fin 32 → List BSym) (R : RegFile)
    (out : List BSym) : Fin 32 → List BSym :=
  regStore (Function.update frame 5 out) R

lemma regStore_at_data (frame : Fin 32 → List BSym) (R : RegFile) :
    regStore frame R 7 = frame 7 := by
  rw [regStore, port_write_outside _ _ _ _ (by decide)]
  rfl

@[simp] lemma outputStore_data (frame : Fin 32 → List BSym) (R : RegFile)
    (out : List BSym) : outputStore frame R out 7 = frame 7 := by
  simp [outputStore, regStore_at_data]

/-- The only additional implementation obligation beyond the checked register backend. -/
structure OutputBackend where
  writer : StackProg (Fin 32) BSym
  C : ℕ
  writer_ok : ∀ (frame : Fin 32 → List BSym) (R : RegFile) (out : List BSym),
    ∃ n, writer.Exec (outputStore frame R out)
      (outputStore frame (resetCounts R)
        (TensorNP.Eigen.encRat ((R 14 : ℚ) - (R 15 : ℚ)) ++ out)) n ∧
      n ≤ C * (R 14 + R 15 + 2)^2


end TensorNP.BilinearEncoder
end


/- Inlined module: OutputCompiler -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

/-- The weighted output semantics compiles to an actual finite-stack execution. -/
theorem compileOutput_sound (B : OutputBackend) {data : List BSym} {p : OutputCmd}
    {R T : RegFile} {x y : List BSym} {n : ℕ}
    (h : OutputExec B.C data p R x T y n) (frame : Fin 32 → List BSym)
    (hdata : frame 7 = data) :
    ∃ m, (compileOutput B.writer p).Exec (outputStore frame R x)
      (outputStore frame T y) m ∧ m ≤ n := by
  induction h with
  | reg out he =>
    exact actual_compileReg_sound he (Function.update frame 5 out) (by simpa using hdata)
  | emit R out =>
    exact B.writer_ok frame R out
  | seq hp hq ihp ihq =>
    obtain ⟨u, hu, hub⟩ := ihp
    obtain ⟨v, hv, hvb⟩ := ihq
    exact ⟨u + 1 + v, StackProg.Exec.seq hu hv, by omega⟩
  | @branch less r s yes no R T x y n hp ih =>
    obtain ⟨u, hu, hub⟩ := ih
    have hu' : (if regCompare less r s R then compileOutput B.writer yes else compileOutput B.writer no).Exec
        (outputStore frame R x) (outputStore frame T y) u := by
      split <;> simp_all
    obtain ⟨v, hv, hvb⟩ := actualRegBackend.branch_ok less r s _ _ (Function.update frame 5 x) R (outputStore frame T y) u hu'
    exact ⟨v, hv, by omega⟩
  | downFalse hz =>
    refine ⟨1, ?_, le_rfl⟩
    apply StackProg.Exec.loopFalse
    simp [outputStore, regStore_at, hz]
  | @downTrue r body R S T x y z n m hpos hp hl ihp ihl =>
    obtain ⟨u, hu, hub⟩ := ihp
    obtain ⟨v, hv, hvb⟩ := ihl
    have hg : ((outputStore frame R x (regPorts r)).head?).isSome = true := by
      simp [outputStore, List.head?_replicate, Nat.ne_of_gt hpos]
    refine ⟨1 + (1 + 1 + u) + 1 + v, ?_, by omega⟩
    exact StackProg.Exec.loopTrue hg
      (StackProg.Exec.seq (actualRegBackend.pop_ok (Function.update frame 5 x) R r) hu) hv


end TensorNP.BilinearEncoder
end


/- Inlined module: OutputFrames -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder

namespace TensorNP.BilinearEncoder

lemma outputStore_out (frame : Fin 32 → List BSym) (R : RegFile) (out : List BSym) :
    outputStore frame R out 5 = out := by
  unfold outputStore regStore
  rw [port_write_outside _ _ _ _ (by decide)]
  rfl

lemma outputStore_scratch (frame : Fin 32 → List BSym) (R : RegFile) (out : List BSym)
    (l : Fin 32) (h : regScratch l) : outputStore frame R out l = [] :=
  regStore_scratch (Function.update frame 5 out) R l h

lemma outputStore_count_start (frame : Fin 32 → List BSym) (R : RegFile) (out : List BSym) :
    countWriterStore32 (R 14) (R 15) out (outputStore frame R out) = outputStore frame R out := by
  funext l
  by_cases hl : ∃ r, regPorts r = l
  · obtain ⟨r, rfl⟩ := hl
    have hreg : outputStore frame R out (regPorts r) = List.replicate (R r) .one :=
      regStore_at (Function.update frame 5 out) R r
    unfold countWriterStore32
    rw [hreg]
    fin_cases r <;> simp [regPorts]
  · have h23 : l ≠ 23 := by intro h; apply hl; exact ⟨14, h.symm⟩
    have h24 : l ≠ 24 := by intro h; apply hl; exact ⟨15, h.symm⟩
    by_cases h5 : l = 5
    · subst l
      simp [countWriterStore32, outputStore_out]
    · by_cases hs : regScratch l
      · have hzero := outputStore_scratch frame R out l hs
        simp only [regScratch] at hs
        simp [countWriterStore32, h23, h24, h5, hs, hzero]
      · simp only [regScratch] at hs
        simp [countWriterStore32, h23, h24, h5, hs]

lemma outputStore_count_finish (frame : Fin 32 → List BSym) (R : RegFile) (out newOut : List BSym) :
    countWriterStore32 0 0 newOut (outputStore frame R out) = outputStore frame (resetCounts R) newOut := by
  funext l
  by_cases hl : ∃ r, regPorts r = l
  · obtain ⟨r, rfl⟩ := hl
    have hbefore : outputStore frame R out (regPorts r) = List.replicate (R r) .one :=
      regStore_at (Function.update frame 5 out) R r
    have hafter : outputStore frame (resetCounts R) newOut (regPorts r) =
        List.replicate (resetCounts R r) .one :=
      regStore_at (Function.update frame 5 newOut) (resetCounts R) r
    rw [hafter]
    unfold countWriterStore32
    rw [hbefore]
    fin_cases r <;> simp [regPorts, resetCounts]
  · have hout : ∀ r, regPorts r ≠ l := by intro r h; exact hl ⟨r, h⟩
    have h23 : l ≠ 23 := by intro h; apply hl; exact ⟨14, h.symm⟩
    have h24 : l ≠ 24 := by intro h; apply hl; exact ⟨15, h.symm⟩
    by_cases h5 : l = 5
    · subst l
      simp [countWriterStore32, outputStore_out]
    · by_cases hs : regScratch l
      · have hzero := outputStore_scratch frame (resetCounts R) newOut l hs
        simp only [regScratch] at hs
        simp [countWriterStore32, h23, h24, h5, hs, hzero]
      · have hframe : outputStore frame R out l = outputStore frame (resetCounts R) newOut l := by
          unfold outputStore regStore
          rw [port_write_outside _ _ _ _ hout, port_write_outside _ _ _ _ hout]
          simp [regBase, hs, h5]
        simp only [regScratch] at hs
        simp [countWriterStore32, h23, h24, h5, hs, hframe]

theorem actual_output_backend : Nonempty OutputBackend := by
  obtain ⟨writer, C, hw⟩ := signed_count_writer32
  refine ⟨⟨writer, C, ?_⟩⟩
  intro frame R out
  obtain ⟨n, he, hb⟩ := hw (R 14) (R 15) out (outputStore frame R out)
  rw [outputStore_count_start] at he
  rw [outputStore_count_finish] at he
  exact ⟨n, he, hb⟩

end TensorNP.BilinearEncoder
end


/- Inlined module: NativeOutput -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

/-- One fixed signed writer turns every finite output program into native stack code. -/
theorem output_program_source : ∃ C : ℕ, ∀ p : OutputCmd,
    ∃ source : StackProg (Fin 32) BSym,
      ∀ (data : List BSym) (R T : RegFile) (x y : List BSym) (n : ℕ)
        (frame : Fin 32 → List BSym), frame 7 = data →
        OutputExec C data p R x T y n →
        ∃ m, source.Exec (outputStore frame R x) (outputStore frame T y) m ∧ m ≤ n := by
  obtain ⟨B⟩ := actual_output_backend
  exact ⟨B.C, fun p => ⟨compileOutput B.writer p,
    fun data R T x y n frame hdata h => compileOutput_sound B h frame hdata⟩⟩

end TensorNP.BilinearEncoder
end


/- Inlined module: NaturalHeader -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder

namespace TensorNP.BilinearEncoder

def headerPorts : Fin 12 ↪ Fin 32 := ⟨![27,5,20,21,22,1,7,14,15,16,17,23], by decide⟩
def headerDecode (l : Fin 32) : Option (Fin 12) :=
  if l = 27 then some 0 else if l = 5 then some 1 else if l = 20 then some 2
  else if l = 21 then some 3 else if l = 22 then some 4 else if l = 1 then some 5
  else if l = 7 then some 6 else if l = 14 then some 7 else if l = 15 then some 8
  else if l = 16 then some 9 else if l = 17 then some 10 else if l = 23 then some 11 else none

lemma headerDecode_spec (l : Fin 32) (k : Fin 12) :
    headerDecode l = some k ↔ headerPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

lemma outputStore_at (frame : Fin 32 → List BSym) (R : RegFile) (out : List BSym) (r : Fin 21) :
    outputStore frame R out (regPorts r) = List.replicate (R r) .one :=
  regStore_at (Function.update frame 5 out) R r

lemma outputStore_other (frame : Fin 32 → List BSym) (R : RegFile) (out out' : List BSym)
    (l : Fin 32) (h5 : l ≠ 5) : outputStore frame R out l = outputStore frame R out' l := by
  by_cases h : ∃ r, regPorts r = l
  · obtain ⟨r, rfl⟩ := h
    rw [outputStore_at, outputStore_at]
  · have hout : ∀ r, regPorts r ≠ l := by intro r hr; exact h ⟨r, hr⟩
    unfold outputStore regStore
    rw [port_write_outside _ _ _ _ hout, port_write_outside _ _ _ _ hout]
    simp [regBase, h5]

def headerWriterFrame (frame : Fin 32 → List BSym) (R : RegFile) : Fin 7 → List BSym :=
  ![List.replicate (R 0) .one, frame 7, List.replicate (R 10) .one,
    List.replicate (R 11) .one, List.replicate (R 12) .one,
    List.replicate (R 13) .one, List.replicate (R 14) .one]

lemma header_project (frame : Fin 32 → List BSym) (R : RegFile) (out : List BSym) :
    StackProgPortLift.project headerPorts (outputStore frame R out) =
      writerStore12 (R 16) out (headerWriterFrame frame R) := by
  have h27 : outputStore frame R out 27 = List.replicate (R 16) .one := outputStore_at frame R out 16
  have h1 : outputStore frame R out 1 = List.replicate (R 0) .one := outputStore_at frame R out 0
  have h14 : outputStore frame R out 14 = List.replicate (R 10) .one := outputStore_at frame R out 10
  have h15 : outputStore frame R out 15 = List.replicate (R 11) .one := outputStore_at frame R out 11
  have h16 : outputStore frame R out 16 = List.replicate (R 12) .one := outputStore_at frame R out 12
  have h17 : outputStore frame R out 17 = List.replicate (R 13) .one := outputStore_at frame R out 13
  have h23 : outputStore frame R out 23 = List.replicate (R 14) .one := outputStore_at frame R out 14
  have h20 := outputStore_scratch frame R out 20 (by decide)
  have h21 := outputStore_scratch frame R out 21 (by decide)
  have h22 := outputStore_scratch frame R out 22 (by decide)
  funext k
  fin_cases k <;> simp [StackProgPortLift.project, headerPorts, writerStore12, headerWriterFrame,
    h27, h1, h14, h15, h16, h17, h23, h20, h21, h22, outputStore_out, outputStore_data]

lemma header_write (frame : Fin 32 → List BSym) (R : RegFile) (out out' : List BSym) :
    StackProgPortLift.write headerPorts (writerStore12 (R 16) out' (headerWriterFrame frame R))
      (outputStore frame R out) = outputStore frame R out' := by
  classical
  funext l
  by_cases h : ∃ k, headerPorts k = l
  · obtain ⟨k, rfl⟩ := h
    rw [port_write_at]
    exact (congrFun (header_project frame R out') k).symm
  · have h5 : l ≠ 5 := by intro he; apply h; exact ⟨1, he.symm⟩
    have hout : ∀ k, headerPorts k ≠ l := by intro k hk; exact h ⟨k, hk⟩
    rw [port_write_outside _ _ _ _ hout]
    exact outputStore_other frame R out out' l h5

theorem natural_header_source : ∃ (p : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ (frame : Fin 32 → List BSym) (R : RegFile) (out : List BSym), ∃ n,
      p.Exec (outputStore frame R out) (outputStore frame R (encNat (R 16) ++ out)) n ∧
      n ≤ C*(R 16+1)^2 := by
  obtain ⟨p, C, hp⟩ := nativeWriter12
  refine ⟨StackProgPortLift.liftProgC headerPorts headerDecode p, C, ?_⟩
  intro frame R out
  obtain ⟨n, he, hn⟩ := hp (R 16) out (headerWriterFrame frame R)
  have hlift := StackProgPortLift.liftProgC_exec headerPorts headerDecode headerDecode_spec
    he (outputStore frame R out) (header_project frame R out)
  rw [header_write] at hlift
  exact ⟨n, hlift, hn⟩

end TensorNP.BilinearEncoder
end


/- Inlined module: ThreeHeaders -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder

namespace TensorNP.BilinearEncoder

private lemma headerRegSize_update_le (R : RegFile) (r : Fin 21) (n : ℕ) :
    regSize (Function.update R r n) ≤ regSize R+n := by
  calc
    _ ≤ ∑ k : Fin 21, (R k + if k = r then n else 0) := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k = r <;> simp [hk]
    _ = regSize R+n := by simp [regSize, Finset.sum_add_distrib]

theorem three_headers_source : ∃ (p : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ (frame : Fin 32 → List BSym) (R : RegFile) (out : List BSym), ∃ steps,
      p.Exec (outputStore frame R out)
        (outputStore frame (Function.update R 16 (R 10)) (encNats [R 10, R 6, R 6] ++ out)) steps ∧
      steps ≤ C*(regSize R+1)^2 := by
  obtain ⟨writer, Ch, hw⟩ := natural_header_source
  let assign6 := compileReg actualRegBackend (.assign 16 6)
  let assign10 := compileReg actualRegBackend (.assign 16 10)
  refine ⟨.seq assign6 (.seq writer (.seq writer (.seq assign10 writer))), 3*Ch+1000, ?_⟩
  intro frame R out
  let R1 := Function.update R 16 (R 6)
  let R2 := Function.update R 16 (R 10)
  obtain ⟨a, ha, haB⟩ := actualRegBackend.assign_ok (Function.update frame 5 out) R 16 6
  have ha' : assign6.Exec (outputStore frame R out) (outputStore frame R1 out) a := ha
  have h16 : R1 16 = R 6 := by simp [R1]
  have h10 : R1 10 = R 10 := by simp [R1]
  obtain ⟨b, hb, hbB⟩ := hw frame R1 out
  rw [h16] at hb hbB
  obtain ⟨c, hc, hcB⟩ := hw frame R1 (encNat (R 6) ++ out)
  rw [h16] at hc hcB
  let out2 := encNat (R 6) ++ (encNat (R 6) ++ out)
  obtain ⟨d, hd, hdB⟩ := actualRegBackend.assign_ok (Function.update frame 5 out2) R1 16 10
  have hR2 : Function.update R1 16 (R1 10) = R2 := by
    funext r
    by_cases hr : r = 16 <;> simp [R1, R2, hr]
  rw [hR2] at hd
  have hd' : assign10.Exec (outputStore frame R1 out2) (outputStore frame R2 out2) d := hd
  have hR216 : R2 16 = R 10 := by simp [R2]
  obtain ⟨e, he, heB⟩ := hw frame R2 out2
  rw [hR216] at he heB
  have hseq := StackProg.Exec.seq ha' (StackProg.Exec.seq hb
    (StackProg.Exec.seq hc (StackProg.Exec.seq hd' he)))
  refine ⟨a+1+(b+1+(c+1+(d+1+e))), ?_, ?_⟩
  · simpa [out2, R2, encNats, List.append_assoc] using hseq
  · have hr6 := reg_le_size R 6
    have hr10 := reg_le_size R 10
    have hs : regSize R1 ≤ regSize R+R 6 := headerRegSize_update_le R 16 (R 6)
    have hp6 : (R 6+1)^2 ≤ (regSize R+1)^2 := Nat.pow_le_pow_left (by omega) 2
    have hp10 : (R 10+1)^2 ≤ (regSize R+1)^2 := Nat.pow_le_pow_left (by omega) 2
    have hbB' := hbB.trans (Nat.mul_le_mul_left Ch hp6)
    have hcB' := hcB.trans (Nat.mul_le_mul_left Ch hp6)
    have heB' := heB.trans (Nat.mul_le_mul_left Ch hp10)
    have hsq : regSize R+1 ≤ (regSize R+1)^2 := Nat.le_self_pow (by decide) _
    simp only [regCharge] at haB hdB
    nlinarith

end TensorNP.BilinearEncoder
end


/- Inlined module: EntryCounterSteps -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

lemma reg_update_self (R : RegFile) (r : Fin 21) : Function.update R r (R r) = R := by
  funext k
  by_cases hk : k=r <;> simp [hk]

lemma regSize_update_le (R : RegFile) (r : Fin 21) (n : ℕ) :
    regSize (Function.update R r n) ≤ regSize R+n := by
  calc
    _ ≤ ∑ k : Fin 21, (R k + if k=r then n else 0) := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k=r <;> simp [hk]
    _ = regSize R+n := by simp [regSize, Finset.sum_add_distrib]

def monoInc (target row col : Fin 21) : RegCmd :=
  .branch false row 1 (.branch false col 2 (.inc target) .skip) .skip

theorem monoInc_exec (data : List BSym) (R : RegFile) (target row col : Fin 21) :
    ∃ steps, RegExec data (monoInc target row col) R
      (Function.update R target (R target+naturalMonomial (R row) (R col) (R 1) (R 2))) steps ∧
      steps ≤ 3*regCharge R+2 := by
  by_cases hr : R row=R 1
  · by_cases hc : R col=R 2
    · have he := RegExec.branch (data := data) (R := R) (yes := .branch false col 2 (.inc target) .skip) (no := .skip)
        (less := false) (r := row) (s := 1)
        (by simpa [regCompare, hr] using
          (RegExec.branch (data := data) (R := R) (yes := .inc target) (no := .skip) (less := false) (r := col) (s := 2)
            (by simpa [regCompare, hc] using RegExec.inc (data := data) R target)))
      refine ⟨regCharge R+(regCharge R+regCharge R), ?_, by omega⟩
      simpa [monoInc, naturalMonomial, hr, hc] using he
    · have he := RegExec.branch (data := data) (R := R) (yes := .branch false col 2 (.inc target) .skip) (no := .skip)
        (less := false) (r := row) (s := 1)
        (by simpa [regCompare, hr] using
          (RegExec.branch (data := data) (R := R) (yes := .inc target) (no := .skip) (less := false) (r := col) (s := 2)
            (by simpa [regCompare, hc] using RegExec.skip (data := data) R)))
      refine ⟨regCharge R+(regCharge R+1), ?_, by omega⟩
      simpa [monoInc, naturalMonomial, hr, hc, reg_update_self] using he
  · have he := RegExec.branch (data := data) (R := R) (yes := .branch false col 2 (.inc target) .skip) (no := .skip)
      (less := false) (r := row) (s := 1)
      (by simpa [regCompare, hr] using RegExec.skip (data := data) R)
    refine ⟨regCharge R+1, ?_, by omega⟩
    simpa [monoInc, naturalMonomial, hr, reg_update_self] using he

end TensorNP.Encoder
end


/- Inlined module: EncoderInit -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def encoderRegs (v : ℕ) : RegFile := Function.update (fun _ : Fin 21 => 0) 0 v

theorem encoderRegs_size (v : ℕ) : regSize (encoderRegs v) = v := by
  simp [regSize, encoderRegs, Fin.sum_univ_succ]

theorem frontendGraphStore_eq_outputStore (input data : List BSym) (v : ℕ) :
    frontendGraphStore input v data = outputStore (frontendGraphStore input v data) (encoderRegs v) [] := by
  classical
  funext l
  by_cases hex : ∃ r, regPorts r = l
  · obtain ⟨r, rfl⟩ := hex
    rw [outputStore, regStore_at]
    fin_cases r <;> simp [encoderRegs, regPorts, frontendGraphStore, frontendStore]
  · have hout : ∀ r, regPorts r ≠ l := by intro r hr; exact hex ⟨r, hr⟩
    rw [outputStore, regStore, port_write_outside _ _ _ _ hout]
    fin_cases l <;> simp [regBase, regScratch, frontendGraphStore, frontendStore]

def dimensionInit (doubled : Bool) : RegCmd :=
  .seq (.assign 7 0) (.seq (.add 7 0 (by decide)) (.seq (.inc 7)
    (if doubled then .seq (.assign 6 7) (.add 6 7 (by decide)) else .assign 6 7)))

def dimensionState (doubled : Bool) (R : RegFile) : RegFile :=
  Function.update (Function.update R 7 (2*R 0+1)) 6
    (if doubled then (2*R 0+1)+(2*R 0+1) else 2*R 0+1)

theorem dimensionInit_exec (doubled : Bool) (data : List BSym) (R : RegFile) :
    ∃ n, RegExec data (dimensionInit doubled) R (dimensionState doubled R) n ∧
      n ≤ 10000*(regSize R+1) := by
  let A := Function.update R 7 (R 0)
  let B := Function.update A 7 (2*R 0)
  let D := Function.update B 7 (2*R 0+1)
  let E := Function.update D 6 (2*R 0+1)
  let F := Function.update E 6 ((2*R 0+1)+(2*R 0+1))
  have he1 : RegExec data (.assign 7 0) R A (regCharge R) := RegExec.assign R 7 0
  have hv2 : R 0 + R 0 = 2*R 0 := by omega
  have he2 : RegExec data (.add 7 0 (by decide)) A B (regCharge A) := by
    simpa [A, B, hv2] using RegExec.add (data := data) A 7 0 (by decide)
  have he3 : RegExec data (.inc 7) B D (regCharge B) := by
    simpa [A, B, D] using RegExec.inc (data := data) B 7
  have he4 : RegExec data (.assign 6 7) D E (regCharge D) := by
    simpa [A, B, D, E] using RegExec.assign (data := data) D 6 7
  have he5 : RegExec data (.add 6 7 (by decide)) E F (regCharge E) := by
    simpa [A, B, D, E, F] using RegExec.add (data := data) E 6 7 (by decide)
  have hE : E = dimensionState false R := by
    funext k
    fin_cases k <;> simp [A, B, D, E, dimensionState]
  have hF : F = dimensionState true R := by
    funext k
    fin_cases k <;> simp [A, B, D, E, F, dimensionState]
  have h0 := reg_le_size R 0
  have ha := regSize_update_le R 7 (R 0)
  change regSize A ≤ _ at ha
  have hb := regSize_update_le A 7 (2*R 0)
  change regSize B ≤ _ at hb
  have hd := regSize_update_le B 7 (2*R 0+1)
  change regSize D ≤ _ at hd
  have he := regSize_update_le D 6 (2*R 0+1)
  change regSize E ≤ _ at he
  cases doubled with
  | false =>
      rw [hE] at he4
      have hex := RegExec.seq he1 (RegExec.seq he2 (RegExec.seq he3 he4))
      refine ⟨_, hex, ?_⟩
      simp only [regCharge]
      omega
  | true =>
      rw [hF] at he5
      have hex := RegExec.seq he1 (RegExec.seq he2 (RegExec.seq he3 (RegExec.seq he4 he5)))
      refine ⟨_, hex, ?_⟩
      simp only [regCharge]
      omega

@[simp] theorem dimensionState_at0 (doubled : Bool) (R : RegFile) : dimensionState doubled R 0 = R 0 := by
  simp [dimensionState]
@[simp] theorem dimensionState_at7 (doubled : Bool) (R : RegFile) : dimensionState doubled R 7 = 2*R 0+1 := by
  simp [dimensionState]
@[simp] theorem dimensionState_at6 (doubled : Bool) (R : RegFile) : dimensionState doubled R 6 =
    (if doubled then (2*R 0+1)+(2*R 0+1) else 2*R 0+1) := by
  simp [dimensionState]

theorem dimensionState_other (doubled : Bool) (R : RegFile) (r : Fin 21)
    (h7 : r ≠ 7) (h6 : r ≠ 6) : dimensionState doubled R r = R r := by
  simp [dimensionState, h7, h6]

theorem dimensionState_encoderRegs_size (doubled : Bool) (v : ℕ) :
    regSize (dimensionState doubled (encoderRegs v)) ≤ 10*(v+1) := by
  have h1 := regSize_update_le (encoderRegs v) 7 (2*(encoderRegs v 0)+1)
  have h2 := regSize_update_le (Function.update (encoderRegs v) 7 (2*(encoderRegs v 0)+1)) 6
    (if doubled then (2*(encoderRegs v 0)+1)+(2*(encoderRegs v 0)+1) else 2*(encoderRegs v 0)+1)
  change regSize (dimensionState doubled (encoderRegs v)) ≤ _ at h2
  simp only [encoderRegs_size] at h1
  have h0 : encoderRegs v 0 = v := by simp [encoderRegs]
  rw [h0] at h1 h2
  cases doubled <;> simp_all <;> omega

end TensorNP.BilinearEncoder
end


/- Inlined module: BodyPoly -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

theorem graph_payload_poly_of_output (payload : ℕ → List BSym → List BSym)
    (body : OutputCmd) (d : ℕ)
    (hbody : ∀ C, ∃ A, ∀ v (G : SimpleGraph (Fin v)),
      ∃ (T : RegFile) (word : List BSym) (n : ℕ),
        OutputExec C (graphData G) body (encoderRegs v) [] T word n ∧
        n ≤ A * (v + 1)^d ∧ regSize T + 1 ≤ A * (v + 1)^d ∧
        encNats [T 10, T 6, T 6] ++ word = payload v (graphData G)) :
    CookPvsNP.PolyTimeComputable (graphEncoderValue payload) := by
  obtain ⟨C, hC⟩ := output_program_source
  obtain ⟨source, hsource⟩ := hC body
  obtain ⟨A, hA⟩ := hbody C
  obtain ⟨headers, Ch, hheaders⟩ := three_headers_source
  apply graph_encoder_polytime_of_backend payload (.seq source headers) (A + Ch * A^2 + 1) (2*d)
  intro input v G
  obtain ⟨T, word, n, he, hn, hs, hw⟩ := hA v G
  let frame := frontendGraphStore input v (graphData G)
  obtain ⟨m, hm, hmb⟩ := hsource (graphData G) (encoderRegs v) T [] word n frame
    (by simp [frame, frontendGraphStore, frontendStore]) he
  obtain ⟨k, hk, hkb⟩ := hheaders frame T word
  refine ⟨outputStore frame (Function.update T 16 (T 10)) (encNats [T 10, T 6, T 6] ++ word),
    m + 1 + k, ?_, ?_, ?_⟩
  · simpa only [frame, ← frontendGraphStore_eq_outputStore] using StackProg.Exec.seq hm hk
  · have hp := Nat.pow_le_pow_left hs 2
    have hk' : k ≤ Ch * A^2 * (v + 1)^(2*d) := by
      calc
        k ≤ Ch * (regSize T + 1)^2 := hkb
        _ ≤ Ch * (A * (v + 1)^d)^2 := Nat.mul_le_mul_left Ch hp
        _ = Ch * A^2 * (v + 1)^(2*d) := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm d 2]
          ring
    have hpow : (v + 1)^d ≤ (v + 1)^(2*d) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hm' : m ≤ A * (v + 1)^(2*d) := (hmb.trans hn).trans (Nat.mul_le_mul_left A hpow)
    have hpos : 1 ≤ (v + 1)^(2*d) := Nat.pow_pos (by omega : 0 < v + 1)
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  · simpa only [outputStore_out] using hw

end TensorNP.BilinearEncoder
end


/- Inlined module: ScanState -/
section
set_option autoImplicit false
open TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def minorScanState (R : RegFile) (a b L : ℕ) : RegFile :=
  Function.update (Function.update (Function.update R 18 a) 19 b) 10 L

def vertexScanState (R : RegFile) (i L : ℕ) : RegFile :=
  Function.update (Function.update R 3 i) 10 L

@[simp] theorem minorScanState_at18 (R : RegFile) (a b L : ℕ) : minorScanState R a b L 18 = a := by
  simp [minorScanState]
@[simp] theorem minorScanState_at19 (R : RegFile) (a b L : ℕ) : minorScanState R a b L 19 = b := by
  simp [minorScanState]
@[simp] theorem minorScanState_at10 (R : RegFile) (a b L : ℕ) : minorScanState R a b L 10 = L := by
  simp [minorScanState]

theorem minorScanState_other (R : RegFile) (a b L : ℕ) (r : Fin 21)
    (h18 : r ≠ 18) (h19 : r ≠ 19) (h10 : r ≠ 10) : minorScanState R a b L r = R r := by
  simp [minorScanState, h18, h19, h10]

@[simp] theorem minorScanState_at7 (R : RegFile) (a b L : ℕ) : minorScanState R a b L 7 = R 7 := by
  simp [minorScanState]

@[simp] theorem vertexScanState_at3 (R : RegFile) (i L : ℕ) : vertexScanState R i L 3 = i := by
  simp [vertexScanState]
@[simp] theorem vertexScanState_at10 (R : RegFile) (i L : ℕ) : vertexScanState R i L 10 = L := by
  simp [vertexScanState]

theorem vertexScanState_other (R : RegFile) (i L : ℕ) (r : Fin 21)
    (h3 : r ≠ 3) (h10 : r ≠ 10) : vertexScanState R i L r = R r := by
  simp [vertexScanState, h3, h10]

theorem minorScanState_down19 (R : RegFile) (a b L : ℕ) :
    Function.update (minorScanState R a (b+1) L) 19 (minorScanState R a (b+1) L 19 - 1) =
      minorScanState R a b L := by
  funext k
  by_cases h18 : k = 18 <;> by_cases h19 : k = 19 <;> by_cases h10 : k = 10 <;>
    simp [minorScanState, Function.update, h18, h19, h10]

theorem minorScanState_inc10 (R : RegFile) (a b L : ℕ) :
    Function.update (minorScanState R a b L) 10 (minorScanState R a b L 10 + 1) =
      minorScanState R a b (L+1) := by
  funext k
  by_cases h18 : k = 18 <;> by_cases h19 : k = 19 <;> by_cases h10 : k = 10 <;>
    simp [minorScanState, Function.update, h18, h19, h10]

theorem minorScanState_down18 (R : RegFile) (a b L : ℕ) :
    Function.update (minorScanState R (a+1) b L) 18 (minorScanState R (a+1) b L 18 - 1) =
      minorScanState R a b L := by
  funext k
  by_cases h18 : k = 18 <;> by_cases h19 : k = 19 <;> by_cases h10 : k = 10 <;>
    simp [minorScanState, Function.update, h18, h19, h10]

theorem minorScanState_set19_from7 (R : RegFile) (a b L : ℕ) :
    Function.update (minorScanState R a b L) 19 (minorScanState R a b L 7) =
      minorScanState R a (R 7) L := by
  funext k
  by_cases h18 : k = 18 <;> by_cases h19 : k = 19 <;> by_cases h10 : k = 10 <;>
    simp [minorScanState, Function.update, h18, h19, h10]

theorem minorScanState_set19_from7_eq (R : RegFile) (a b L N : ℕ) (h7 : R 7 = N) :
    Function.update (minorScanState R a b L) 19 (minorScanState R a b L 7) = minorScanState R a N L := by
  simpa only [h7] using minorScanState_set19_from7 R a b L

theorem vertexScanState_down3 (R : RegFile) (i L : ℕ) :
    Function.update (vertexScanState R (i+1) L) 3 (vertexScanState R (i+1) L 3 - 1) =
      vertexScanState R i L := by
  funext k
  by_cases h3 : k = 3 <;> by_cases h10 : k = 10 <;>
    simp [vertexScanState, Function.update, h3, h10]

theorem vertexScanState_inc10 (R : RegFile) (i L : ℕ) :
    Function.update (vertexScanState R i L) 10 (vertexScanState R i L 10 + 1) =
      vertexScanState R i (L+1) := by
  funext k
  by_cases h3 : k = 3 <;> by_cases h10 : k = 10 <;>
    simp [vertexScanState, Function.update, h3, h10]

theorem minorScanState_size (R : RegFile) (a b L : ℕ) :
    regSize (minorScanState R a b L) ≤ regSize R + a + b + L := by
  have ha := regSize_update_le R 18 a
  have hb := regSize_update_le (Function.update R 18 a) 19 b
  have hL := regSize_update_le (Function.update (Function.update R 18 a) 19 b) 10 L
  change regSize (minorScanState R a b L) ≤ _ at hL
  omega

theorem vertexScanState_size (R : RegFile) (i L : ℕ) :
    regSize (vertexScanState R i L) ≤ regSize R + i + L := by
  have hi := regSize_update_le R 3 i
  have hL := regSize_update_le (Function.update R 3 i) 10 L
  change regSize (vertexScanState R i L) ≤ _ at hL
  omega

end TensorNP.BilinearEncoder
end


/- Inlined module: SliceScan -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

/-- How many slices an ascending prefix contributes to the dimension header. -/
def scanCount (inc : ℕ → ℕ) (count : ℕ) : ℕ :=
  ((List.range count).map inc).sum

def scanChunk (E : ℕ → List BSym) (count : ℕ) : List BSym :=
  (List.range count).flatMap E

/-- A descending scan can prepend slices while accumulating their total count.
The cap bounds the live unary header counter throughout the native computation. -/
theorem sliceScan_exec (C : ℕ) (data : List BSym) (body : OutputCmd) (r : Fin 21)
    (state : ℕ → ℕ → RegFile) (E : ℕ → List BSym) (inc : ℕ → ℕ) (N B cap : ℕ)
    (hat : ∀ i L, state i L r = i)
    (hdown : ∀ i L, Function.update (state (i + 1) L) r
      (state (i + 1) L r - 1) = state i L)
    (hbody : ∀ i L tail, i < N → L + inc i ≤ cap →
      ∃ n, OutputExec C data body (state i L) tail
        (state i (L + inc i)) (E i ++ tail) n ∧ n ≤ B)
    (count : ℕ) (hc : count ≤ N) (L : ℕ) (hcap : L + scanCount inc count ≤ cap)
    (tail : List BSym) :
    ∃ steps, OutputExec C data (.down r body) (state count L) tail
      (state 0 (L + scanCount inc count)) (scanChunk E count ++ tail) steps ∧
      steps ≤ count * (B + 5) + 1 := by
  induction count generalizing L tail with
  | zero =>
    exact ⟨1, by simpa [scanCount, scanChunk] using
      (OutputExec.downFalse (C := C) (data := data) (body := body) (out := tail) (hat 0 L)), by simp⟩
  | succ count ih =>
    have hcount : scanCount inc (count + 1) = scanCount inc count + inc count := by
      simp [scanCount, List.range_succ]
    have hlocal : L + inc count ≤ cap := by omega
    obtain ⟨u, hu, hub⟩ := hbody count L tail (by omega) hlocal
    obtain ⟨v, hv, hvb⟩ := ih (by omega) (L + inc count) (by omega) (E count ++ tail)
    have hstep : OutputExec C data body
        (Function.update (state (count + 1) L) r (state (count + 1) L r - 1)) tail
        (state count (L + inc count)) (E count ++ tail) u := by
      simpa only [hdown count L] using hu
    have he := OutputExec.downTrue (r := r) (R := state (count + 1) L)
      (by simpa only [hat] using Nat.succ_pos count) hstep hv
    have hfinal : L + inc count + scanCount inc count = L + scanCount inc (count + 1) := by
      omega
    refine ⟨u + v + 5, ?_, ?_⟩
    · simpa [hfinal, scanChunk, List.range_succ, List.flatMap_append,
        List.append_assoc] using he
    · rw [Nat.add_mul, Nat.one_mul]
      omega

end TensorNP.BilinearEncoder
end


/- Inlined module: NeighborCounter -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def neighborTriple : RegCmd :=
  .seq (monoInc 14 3 3) (.seq (monoInc 14 3 8) (monoInc 14 8 8))

def neighborDelta (data : List BSym) (R : RegFile) : ℕ :=
  if data.getD (R 3*R 0+R 8) .zero = .one then
    naturalMonomial (R 3) (R 3) (R 1) (R 2) +
    naturalMonomial (R 3) (R 8) (R 1) (R 2) +
    naturalMonomial (R 8) (R 8) (R 1) (R 2) else 0

def neighborBody : RegCmd := .neighbor neighborTriple .skip

theorem neighborTriple_exec (data : List BSym) (R : RegFile) :
    ∃ steps, RegExec data neighborTriple R
      (Function.update R 14 (R 14 + naturalMonomial (R 3) (R 3) (R 1) (R 2) +
        naturalMonomial (R 3) (R 8) (R 1) (R 2) +
        naturalMonomial (R 8) (R 8) (R 1) (R 2))) steps ∧
      steps ≤ 2000*(regSize R+2) := by
  let a := naturalMonomial (R 3) (R 3) (R 1) (R 2)
  let b := naturalMonomial (R 3) (R 8) (R 1) (R 2)
  let c := naturalMonomial (R 8) (R 8) (R 1) (R 2)
  let S1 := Function.update R 14 (R 14+a)
  let S2 := Function.update R 14 (R 14+a+b)
  let S3 := Function.update R 14 (R 14+a+b+c)
  obtain ⟨m1, he1, hb1⟩ := monoInc_exec data R 14 3 3
  change RegExec data (monoInc 14 3 3) R S1 m1 at he1
  obtain ⟨m2, he2, hb2⟩ := monoInc_exec data S1 14 3 8
  have hu2 : Function.update S1 14
      (S1 14+naturalMonomial (S1 3) (S1 8) (S1 1) (S1 2)) = S2 := by
    funext k
    by_cases hk : k=14 <;> simp [S1, S2, b, hk]
  rw [hu2] at he2
  obtain ⟨m3, he3, hb3⟩ := monoInc_exec data S2 14 8 8
  have hu3 : Function.update S2 14
      (S2 14+naturalMonomial (S2 8) (S2 8) (S2 1) (S2 2)) = S3 := by
    funext k
    by_cases hk : k=14 <;> simp [S2, S3, c, hk]
  rw [hu3] at he3
  refine ⟨m1+1+(m2+1+m3), RegExec.seq he1 (RegExec.seq he2 he3), ?_⟩
  have ha : a≤1 := naturalMonomial_le _ _ _ _
  have hb : b≤1 := naturalMonomial_le _ _ _ _
  have hsize1 : regSize S1 ≤ regSize R+R 14+a := by
    simpa [S1, Nat.add_assoc] using regSize_update_le R 14 (R 14+a)
  have hsize2 : regSize S2 ≤ regSize R+R 14+a+b := by
    simpa [S2, Nat.add_assoc] using regSize_update_le R 14 (R 14+a+b)
  have hp := reg_le_size R 14
  unfold regCharge at hb1 hb2 hb3
  omega

theorem neighborDelta_le (data : List BSym) (R : RegFile) : neighborDelta data R≤3 := by
  have ha := naturalMonomial_le (R 3) (R 3) (R 1) (R 2)
  have hb := naturalMonomial_le (R 3) (R 8) (R 1) (R 2)
  have hc := naturalMonomial_le (R 8) (R 8) (R 1) (R 2)
  unfold neighborDelta
  split <;> omega

theorem neighborBody_exec (data : List BSym) (R : RegFile)
    (hr : R 3<R 0) (hc : R 8<R 0) (hlen : data.length=R 0*R 0) :
    ∃ steps, RegExec data neighborBody R (Function.update R 14 (R 14+neighborDelta data R)) steps ∧
      steps ≤ 100*(R 0+1)^2+2000*(regSize R+2) := by
  by_cases ha : data.getD (R 3*R 0+R 8) .zero = .one
  · obtain ⟨n, he, hb⟩ := neighborTriple_exec data R
    have he' : RegExec data (if regNeighbor data R then neighborTriple else .skip) R
        (Function.update R 14 (R 14+neighborDelta data R)) n := by
      simpa only [regNeighbor, decide_eq_true_eq, neighborDelta, if_pos ha, Nat.add_assoc] using he
    exact ⟨100*(R 0+1)^2+n, RegExec.neighbor hr hc hlen he', by omega⟩
  · have he' : RegExec data (if regNeighbor data R then neighborTriple else .skip) R
        (Function.update R 14 (R 14+neighborDelta data R)) 1 := by
      simpa only [regNeighbor, decide_eq_true_eq, neighborDelta, if_neg ha, Nat.add_zero, reg_update_self] using RegExec.skip (data := data) R
    exact ⟨100*(R 0+1)^2+1, RegExec.neighbor hr hc hlen he', by omega⟩

def neighborFrame (base : RegFile) (count total : ℕ) : RegFile :=
  Function.update (Function.update base 8 count) 14 total

lemma neighborFrame_size (base : RegFile) (count total : ℕ) :
    regSize (neighborFrame base count total) ≤ regSize base+count+total := by
  exact (regSize_update_le _ 14 total).trans (Nat.add_le_add_right (regSize_update_le base 8 count) total)

lemma neighborFrame_delta (data : List BSym) (base : RegFile) (count total : ℕ) :
    neighborDelta data (neighborFrame base count total) =
      if data.getD (base 3*base 0+count) .zero = .one then
        naturalMonomial (base 3) (base 3) (base 1) (base 2) +
        naturalMonomial (base 3) count (base 1) (base 2) +
        naturalMonomial count count (base 1) (base 2) else 0 := by
  simp [neighborDelta, neighborFrame]

theorem neighborLoop_exec (data : List BSym) (base : RegFile) (cap : ℕ)
    (hr : base 3<base 0) (hlen : data.length=base 0*base 0) :
    ∀ count : ℕ, count≤base 0 → ∀ total : ℕ, total+3*count≤cap → ∃ steps,
      RegExec data (.down 8 neighborBody) (neighborFrame base count total)
        (neighborFrame base 0 (total+neighborCount (base 0) data (base 3) (base 1) (base 2) count)) steps ∧
      steps ≤ count*(100*(base 0+1)^2+2000*(regSize base+base 0+cap+2)+5)+1 := by
  intro count
  induction count with
  | zero =>
      intro _ total _
      refine ⟨1, ?_, by simp⟩
      simpa [neighborCount] using
        (RegExec.downFalse (data := data) (r := 8) (body := neighborBody)
          (R := neighborFrame base 0 total) (by simp [neighborFrame]))
  | succ count ih =>
      intro hc total hcap
      let R := neighborFrame base count total
      let delta := neighborDelta data R
      have hdelta : delta≤3 := neighborDelta_le data R
      obtain ⟨n, he, hb⟩ := neighborBody_exec data R
        (by simpa [R, neighborFrame] using hr)
        (by simpa [R, neighborFrame] using (show count<base 0 by omega))
        (by simpa [R, neighborFrame] using hlen)
      have hu : Function.update R 14 (R 14+neighborDelta data R) =
          neighborFrame base count (total+delta) := by
        funext k
        by_cases hk : k=14 <;> simp [R, neighborFrame, delta, hk]
      rw [hu] at he
      obtain ⟨m, hm, hmb⟩ := ih (by omega) (total+delta) (by omega)
      have hpop : Function.update (neighborFrame base (count+1) total) 8
          (neighborFrame base (count+1) total 8-1) = R := by
        funext k
        by_cases hk8 : k=8 <;> by_cases hk14 : k=14 <;> simp_all [R, neighborFrame]
      have he' := RegExec.downTrue (r := 8) (body := neighborBody)
        (R := neighborFrame base (count+1) total) (by simp [neighborFrame])
        (hpop ▸ he) hm
      have hout : total+delta+neighborCount (base 0) data (base 3) (base 1) (base 2) count =
          total+neighborCount (base 0) data (base 3) (base 1) (base 2) (count+1) := by
        rw [neighborCount]
        change total+neighborDelta data (neighborFrame base count total)+_ = _
        rw [neighborFrame_delta]
        omega
      rw [hout] at he'
      refine ⟨n+m+5, he', ?_⟩
      have hs := neighborFrame_size base count total
      have htotal : total≤cap := by omega
      have hR0 : R 0 = base 0 := by simp [R, neighborFrame]
      rw [hR0] at hb
      have hsR : regSize R ≤ regSize base+count+total := hs
      have hcount : count ≤ base 0 := (Nat.le_succ count).trans hc
      have hsizeCap : regSize R ≤ regSize base+base 0+cap :=
        hsR.trans (Nat.add_le_add (Nat.add_le_add_left hcount _) htotal)
      have hb' : n ≤ 100*(base 0+1)^2+2000*(regSize base+base 0+cap+2) :=
        hb.trans (Nat.add_le_add_left
          (Nat.mul_le_mul_left 2000 (Nat.add_le_add_right hsizeCap 2)) _)
      rw [Nat.add_mul]
      omega


def neighborFamily : RegCmd := .seq (.assign 8 0) (.down 8 neighborBody)

theorem neighborFamily_exec (data : List BSym) (R : RegFile)
    (hr : R 3<R 0) (hlen : data.length=R 0*R 0) (h8 : R 8=0) (h14 : R 14=0) :
    ∃ steps, RegExec data neighborFamily R
      (Function.update R 14 (neighborCount (R 0) data (R 3) (R 1) (R 2) (R 0))) steps ∧
      steps ≤ regCharge R+1+
        (R 0*(100*(R 0+1)^2+2000*(regSize R+4*R 0+2)+5)+1) := by
  obtain ⟨n, he, hb⟩ := neighborLoop_exec data R (3*R 0) hr hlen (R 0) le_rfl 0 (by omega)
  have hstart : neighborFrame R (R 0) 0 = Function.update R 8 (R 0) := by
    funext k
    by_cases hk : k=14 <;> simp [neighborFrame, hk, h14]
  have hend : neighborFrame R 0
      (0+neighborCount (R 0) data (R 3) (R 1) (R 2) (R 0)) =
      Function.update R 14 (neighborCount (R 0) data (R 3) (R 1) (R 2) (R 0)) := by
    funext k
    by_cases hk8 : k=8 <;> by_cases hk14 : k=14 <;> simp_all [neighborFrame]
  rw [hstart, hend] at he
  refine ⟨regCharge R+1+n, RegExec.seq (RegExec.assign R 8 0) he, ?_⟩
  nlinarith

end TensorNP.Encoder
end


/- Inlined module: SmallFamilies -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def smallFamily (f : Fin 3) : RegCmd :=
  ![.seq (monoInc 14 3 9) (monoInc 15 4 4),
    .seq (monoInc 14 9 4) (monoInc 15 3 3),
    .seq (monoInc 14 3 4) (monoInc 15 9 9)] f

lemma monoPair_exec (data : List BSym) (R : RegFile) (pr pc nr nc : Fin 21)
    (hnr : nr ≠ 14) (hnc : nc ≠ 14) :
    ∃ steps, RegExec data (.seq (monoInc 14 pr pc) (monoInc 15 nr nc)) R
      (Function.update (Function.update R 14
        (R 14 + naturalMonomial (R pr) (R pc) (R 1) (R 2))) 15
        (R 15 + naturalMonomial (R nr) (R nc) (R 1) (R 2))) steps ∧
      steps ≤ 10000*(regSize R+2) := by
  let p := naturalMonomial (R pr) (R pc) (R 1) (R 2)
  let S := Function.update R 14 (R 14+p)
  obtain ⟨m, hm, hmB⟩ := monoInc_exec data R 14 pr pc
  obtain ⟨n, hn, hnB⟩ := monoInc_exec data S 15 nr nc
  have he := RegExec.seq hm hn
  have he' : RegExec data (.seq (monoInc 14 pr pc) (monoInc 15 nr nc)) R
      (Function.update S 15 (R 15 + naturalMonomial (R nr) (R nc) (R 1) (R 2))) (m+1+n) := by
    simpa [S, Function.update_of_ne hnr, Function.update_of_ne hnc] using he
  refine ⟨m+1+n, he', ?_⟩
  have hp : p ≤ 1 := naturalMonomial_le _ _ _ _
  have h14 := reg_le_size R 14
  have hS := regSize_update_le R 14 (R 14+p)
  dsimp [S] at hnB
  simp only [regCharge] at hmB hnB
  omega

theorem smallFamily_exec (data : List BSym) (R : RegFile) (f : Fin 3)
    (h4 : R 4 = 2*R 0) (h9 : R 9 = R 0+R 3) :
    ∃ steps, RegExec data (smallFamily f) R
      (Function.update (Function.update R 14
        (R 14 + rawPositiveCount (R 0) data f.val (R 3) (R 1) (R 2))) 15
        (R 15 + rawNegativeCount (R 0) f.val (R 3) (R 1) (R 2))) steps ∧
      steps ≤ 10000*(regSize R+2) := by
  fin_cases f
  · simpa [smallFamily, rawPositiveCount, rawNegativeCount, ← h4, ← h9] using
      monoPair_exec data R 3 9 4 4 (by decide) (by decide)
  · simpa [smallFamily, rawPositiveCount, rawNegativeCount, ← h4, ← h9] using
      monoPair_exec data R 9 4 3 3 (by decide) (by decide)
  · simpa [smallFamily, rawPositiveCount, rawNegativeCount, ← h4, ← h9] using
      monoPair_exec data R 3 4 9 9 (by decide) (by decide)

end TensorNP.Encoder
end


/- Inlined module: ColorFamily -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def colorFamilyBody (f : Fin 4) : RegCmd :=
  ![smallFamily 0, smallFamily 1, smallFamily 2, neighborFamily] f

def colorFamily (f : Fin 4) : RegCmd :=
  .seq (.assign 4 0) (.seq (.add 4 0 (by decide)) (.seq (.assign 9 0)
    (.seq (.add 9 3 (by decide)) (.seq (colorFamilyBody f) (.seq (.reset 4) (.reset 9))))))

lemma colorFamilyBody_exec (data : List BSym) (R : RegFile) (f : Fin 4)
    (hr : R 3 < R 0) (hlen : data.length = R 0 * R 0)
    (h4 : R 4 = 2*R 0) (h9 : R 9 = R 0+R 3) (h8 : R 8 = 0)
    (h14 : R 14 = 0) (h15 : R 15 = 0) :
    ∃ steps, RegExec data (colorFamilyBody f) R
      (Function.update (Function.update R 14
        (rawPositiveCount (R 0) data f.val (R 3) (R 1) (R 2))) 15
        (rawNegativeCount (R 0) f.val (R 3) (R 1) (R 2))) steps ∧
      steps ≤ 5000*(regSize R+2)^3 := by
  have hs := reg_le_size R 0
  have hpow : regSize R+2 ≤ (regSize R+2)^3 := Nat.le_self_pow (by decide) _
  have hpow2 : 2*(regSize R+2) ≤ (regSize R+2)^3 := by nlinarith [Nat.zero_le ((regSize R)^3)]
  fin_cases f
  · obtain ⟨m, he, hb⟩ := smallFamily_exec data R 0 h4 h9
    refine ⟨m, ?_, ?_⟩
    · simpa [colorFamilyBody, h14, h15] using he
    · omega
  · obtain ⟨m, he, hb⟩ := smallFamily_exec data R 1 h4 h9
    refine ⟨m, ?_, ?_⟩
    · simpa [colorFamilyBody, h14, h15] using he
    · omega
  · obtain ⟨m, he, hb⟩ := smallFamily_exec data R 2 h4 h9
    refine ⟨m, ?_, ?_⟩
    · simpa [colorFamilyBody, h14, h15] using he
    · omega
  · obtain ⟨m, he, hb⟩ := neighborFamily_exec data R hr hlen h8 h14
    refine ⟨m, ?_, ?_⟩
    · have hu : Function.update (Function.update R 14
          (neighborCount (R 0) data (R 3) (R 1) (R 2) (R 0))) 15 0 =
          Function.update R 14 (neighborCount (R 0) data (R 3) (R 1) (R 2) (R 0)) := by
        funext r
        by_cases h15r : r = 15 <;> by_cases h14r : r = 14 <;> simp_all
      simpa [colorFamilyBody, rawPositiveCount, rawNegativeCount, hu] using he
    · simp only [regCharge] at hb
      have ha : R 0*(R 0+1)^2 ≤ regSize R*(regSize R+1)^2 :=
        Nat.mul_le_mul hs (Nat.pow_le_pow_left (by omega) 2)
      have hbmul : R 0*(regSize R+4*R 0+2) ≤ regSize R*(5*regSize R+2) :=
        Nat.mul_le_mul hs (by omega)
      nlinarith [Nat.zero_le ((regSize R)^3), Nat.zero_le ((regSize R)^2)]

theorem colorFamily_exec (data : List BSym) (R : RegFile) (f : Fin 4)
    (hr : R 3 < R 0) (hlen : data.length = R 0 * R 0)
    (h4 : R 4 = 0) (h9 : R 9 = 0) (h8 : R 8 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) :
    ∃ steps, RegExec data (colorFamily f) R
      (Function.update (Function.update R 14
        (rawPositiveCount (R 0) data f.val (R 3) (R 1) (R 2))) 15
        (rawNegativeCount (R 0) f.val (R 3) (R 1) (R 2))) steps ∧
      steps ≤ 1000000*(regSize R+2)^4 := by
  let A := Function.update R 4 (R 0)
  let B := Function.update A 4 (A 0 + A 4)
  let C := Function.update B 9 (B 0)
  let S := Function.update C 9 (C 3 + C 9)
  let P := rawPositiveCount (R 0) data f.val (R 3) (R 1) (R 2)
  let M := rawNegativeCount (R 0) f.val (R 3) (R 1) (R 2)
  let T := Function.update (Function.update S 14 P) 15 M
  let U := Function.update T 4 0
  have hS : S = Function.update (Function.update R 4 (2*R 0)) 9 (R 0+R 3) := by
    funext r
    fin_cases r <;> simp [S, C, B, A] <;> omega
  have hs4 : S 4 = 2*S 0 := by simp [hS]
  have hs9 : S 9 = S 0+S 3 := by simp [hS]
  have hs8 : S 8 = 0 := by simpa [hS] using h8
  have hs14 : S 14 = 0 := by simpa [hS] using h14
  have hs15 : S 15 = 0 := by simpa [hS] using h15
  have hsr : S 3 < S 0 := by simpa [hS] using hr
  have hslen : data.length = S 0*S 0 := by simpa [hS] using hlen
  obtain ⟨m, hm, hmB⟩ := colorFamilyBody_exec data S f hsr hslen hs4 hs9 hs8 hs14 hs15
  have hm' : RegExec data (colorFamilyBody f) S T m := by
    simpa [T, P, M, hS] using hm
  have hend : Function.update U 9 0 = Function.update (Function.update R 14 P) 15 M := by
    funext r
    fin_cases r <;> simp [U, T, hS, h4, h9]
  have he := RegExec.seq (RegExec.assign (data := data) R 4 0)
    (RegExec.seq (RegExec.add (data := data) A 4 0 (by decide))
      (RegExec.seq (RegExec.assign (data := data) B 9 0)
        (RegExec.seq (RegExec.add (data := data) C 9 3 (by decide))
          (RegExec.seq hm' (RegExec.seq (RegExec.reset (data := data) T 4)
            (RegExec.reset (data := data) U 9))))))
  rw [hend] at he
  refine ⟨_, he, ?_⟩
  have h0 := reg_le_size R 0
  have h3 := reg_le_size R 3
  have hA := regSize_update_le R 4 (R 0)
  have hB := regSize_update_le A 4 (A 0+A 4)
  have hC := regSize_update_le B 9 (B 0)
  have hTa := regSize_update_le S 14 P
  have hTb := regSize_update_le (Function.update S 14 P) 15 M
  have hU := regSize_update_le T 4 0
  have hPM : P+M ≤ 3*R 0+2 := rawCounts_le (R 0) data f.val (R 3) (R 1) (R 2)
  have hSizeA : regSize A ≤ 2*regSize R := by
    change regSize A ≤ _ at hA
    omega
  have hSizeB : regSize B ≤ 4*regSize R := by
    change regSize B ≤ regSize A+(A 0+A 4) at hB
    simp [A] at hB
    omega
  have hSizeC : regSize C ≤ 5*regSize R := by
    change regSize C ≤ regSize B+B 0 at hC
    have hB0 : B 0 = R 0 := by simp [B, A]
    rw [hB0] at hC
    omega
  have hSa := regSize_update_le R 4 (2*R 0)
  have hSb := regSize_update_le (Function.update R 4 (2*R 0)) 9 (R 0+R 3)
  have hSizeS : regSize S ≤ 5*regSize R := by
    rw [hS]
    omega
  have hSizeT : regSize T ≤ 8*regSize R+2 := by
    change regSize T ≤ regSize (Function.update S 14 P)+M at hTb
    omega
  have hSizeU : regSize U ≤ 8*regSize R+2 := by
    change regSize U ≤ regSize T+0 at hU
    omega
  have hpow : (regSize S+2)^3 ≤ (5*(regSize R+2))^3 :=
    Nat.pow_le_pow_left (by omega) 3
  have hpow' : (regSize S+2)^3 ≤ 125*(regSize R+2)^3 := by
    calc
      _ ≤ (5*(regSize R+2))^3 := hpow
      _ = _ := by ring
  have hquart : (regSize R+2)^3 ≤ (regSize R+2)^4 := pow_le_pow_right₀ (by omega) (by omega)
  have hlinear : regSize R+2 ≤ (regSize R+2)^4 := Nat.le_self_pow (by decide) _
  have hbody : m ≤ 625000*(regSize R+2)^4 := by
    have ht := Nat.mul_le_mul_left 5000 (hpow'.trans (Nat.mul_le_mul_left 125 hquart))
    omega
  simp only [regCharge]
  omega

end TensorNP.Encoder
end


/- Inlined module: CoefficientOutput -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def putCounts (R : RegFile) (P M : ℕ) : RegFile :=
  Function.update (Function.update R 14 P) 15 M

def coeffEmit (p : RegCmd) : OutputCmd := .seq (.reg p) .emit

lemma resetCounts_putCounts (R : RegFile) (P M : ℕ)
    (h14 : R 14 = 0) (h15 : R 15 = 0) :
    resetCounts (putCounts R P M) = R := by
  funext i
  fin_cases i <;> simp [resetCounts, putCounts, h14, h15]

theorem emit_after_coeff {C : ℕ} {data : List BSym} {p : RegCmd}
    {R : RegFile} {n P M : ℕ}
    (he : RegExec data p R (putCounts R P M) n)
    (h14 : R 14 = 0) (h15 : R 15 = 0) (tail : List BSym) :
    OutputExec C data (coeffEmit p) R tail R
      (TensorNP.Eigen.encRat ((P : ℚ) - (M : ℚ)) ++ tail)
      (n + 1 + C * (P + M + 2)^2) := by
  have hr := resetCounts_putCounts R P M h14 h15
  simp [putCounts] at hr
  simpa [coeffEmit, putCounts, hr] using
    (OutputExec.seq (OutputExec.reg tail he) (OutputExec.emit (C := C) (data := data) (putCounts R P M) tail))

end TensorNP.BilinearEncoder
end


/- Inlined module: MatrixEntry -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder

namespace TensorNP.BilinearEncoder

def entryCoords (R : RegFile) : RegFile :=
  Function.update (Function.update R 1 (R 12)) 2 (R 13)

def prepareEntry : RegCmd := .seq (.assign 1 12) (.assign 2 13)
def clearCoords : RegCmd := .seq (.reset 1) (.reset 2)
def matrixEntry (coeff : RegCmd) : OutputCmd :=
  .seq (.reg prepareEntry) (.seq (coeffEmit coeff) (.reg clearCoords))

theorem matrixEntry_exec (C : ℕ) (data : List BSym) (coeff : RegCmd) (R : RegFile)
    (P M B : ℕ) (h1 : R 1 = 0) (h2 : R 2 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0)
    (hcounts : P+M ≤ 3*R 0+2)
    (hcoeff : ∃ n, RegExec data coeff (entryCoords R) (putCounts (entryCoords R) P M) n ∧ n ≤ B)
    (tail : List BSym) :
    ∃ steps, OutputExec C data (matrixEntry coeff) R tail R
      (TensorNP.Eigen.encRat ((P : ℚ) - (M : ℚ)) ++ tail) steps ∧
      steps ≤ B+(16*C+1000000)*(regSize R+2)^2 := by
  let A := Function.update R 1 (R 12)
  let S := entryCoords R
  let U := Function.update S 1 0
  have hA13 : A 13 = R 13 := by simp [A]
  have hprep : RegExec data prepareEntry R S (regCharge R+1+regCharge A) := by
    have he := RegExec.seq (RegExec.assign (data := data) R 1 12)
      (RegExec.assign (data := data) A 2 13)
    simpa [prepareEntry, entryCoords, S, A, hA13] using he
  have hs14 : S 14 = 0 := by simpa [S, entryCoords] using h14
  have hs15 : S 15 = 0 := by simpa [S, entryCoords] using h15
  obtain ⟨n, hn, hnB⟩ := hcoeff
  have hemit := emit_after_coeff (C := C) hn hs14 hs15 tail
  have hfinish : Function.update U 2 0 = R := by
    funext r
    by_cases hr1 : r = 1 <;> by_cases hr2 : r = 2 <;> simp [U, S, entryCoords, h1, h2, hr1, hr2]
  have hclear : RegExec data clearCoords S R (regCharge S+1+regCharge U) := by
    have he := RegExec.seq (RegExec.reset (data := data) S 1) (RegExec.reset (data := data) U 2)
    rw [hfinish] at he
    exact he
  have he := OutputExec.seq (OutputExec.reg (C := C) tail hprep)
    (OutputExec.seq hemit (OutputExec.reg (C := C) _ hclear))
  refine ⟨_, he, ?_⟩
  have hr0 := reg_le_size R 0
  have hr12 := reg_le_size R 12
  have hr13 := reg_le_size R 13
  have hsA : regSize A ≤ regSize R+R 12 := regSize_update_le R 1 (R 12)
  have hsS : regSize S ≤ regSize A+R 13 := by
    have hx := regSize_update_le A 2 (R 13)
    exact hx
  have hsU : regSize U ≤ regSize S := by
    have hx := regSize_update_le S 1 0
    simpa using hx
  have hbase : regSize R+2 ≤ (regSize R+2)^2 := Nat.le_self_pow (by decide) _
  have hsq : (P+M+2)^2 ≤ 16*(regSize R+2)^2 := by
    calc
      _ ≤ (4*(regSize R+2))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have hw := Nat.mul_le_mul_left C hsq
  simp only [regCharge]
  nlinarith

end TensorNP.BilinearEncoder
end


/- Inlined module: MatrixSource -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def matrixProgram (entry : OutputCmd) : OutputCmd :=
  .seq (.reg (.assign 12 6)) (rowLoop entry)

theorem matrixProgram_exec (C : ℕ) (data : List BSym) (entry : OutputCmd)
    (E : ℕ → ℕ → List BSym) (R : RegFile) (N B Q : ℕ)
    (hN : R 6 = N) (h12 : R 12 = 0) (h13 : R 13 = 0)
    (hentry : MatrixEntrySpec C data entry E R N B)
    (hQ : ∀ row, row < N → regCharge (cellState R row 0) ≤ Q) (tail : List BSym) :
    ∃ steps, OutputExec C data (matrixProgram entry) R tail R (matrixChunk E N N ++ tail) steps ∧
      steps ≤ regCharge R+1+(N*(Q+N*(B+5)+7)+1) := by
  have hstart : Function.update R 12 (R 6) = cellState R N 0 := by
    funext r
    by_cases hr12 : r = 12 <;> by_cases hr13 : r = 13 <;> simp [cellState, hN, h13, hr12, hr13]
  have hfinish : cellState R 0 0 = R := by
    funext r
    by_cases hr12 : r = 12 <;> by_cases hr13 : r = 13 <;> simp [cellState, h12, h13, hr12, hr13]
  have he : OutputExec C data (.reg (.assign 12 6)) R tail (cellState R N 0) tail (regCharge R) := by
    simpa only [hstart] using OutputExec.reg (C := C) tail (RegExec.assign (data := data) R 12 6)
  obtain ⟨n, hn, hb⟩ := rowLoop_exec C data entry E R N B Q hN hentry hQ N le_rfl tail
  rw [hfinish] at hn
  exact ⟨regCharge R+1+n, OutputExec.seq he hn, by omega⟩

end TensorNP.BilinearEncoder
end


/- Inlined module: ColorMatrixSource -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def colorEntryWord (v : ℕ) (data : List BSym) (f vertex row col : ℕ) : List BSym :=
  TensorNP.Eigen.encRat ((rawPositiveCount v data f vertex row col : ℚ) -
    (rawNegativeCount v f vertex row col : ℚ))

theorem colorEntry_spec (C : ℕ) (data : List BSym) (R : RegFile) (N : ℕ) (f : Fin 4)
    (hlen : data.length = R 0 * R 0) (hv : R 3 < R 0)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h4 : R 4 = 0) (h8 : R 8 = 0)
    (h9 : R 9 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) :
    MatrixEntrySpec C data (matrixEntry (colorFamily f)) (colorEntryWord (R 0) data f.val (R 3)) R N
      (10000000000*(C+1)*(regSize R+N+2)^4) := by
  intro row col tail hr hc
  let S := cellState R row col
  let T := entryCoords S
  have hs1 : S 1 = 0 := by simpa [S, cellState] using h1
  have hs2 : S 2 = 0 := by simpa [S, cellState] using h2
  have hs14 : S 14 = 0 := by simpa [S, cellState] using h14
  have hs15 : S 15 = 0 := by simpa [S, cellState] using h15
  have ht4 : T 4 = 0 := by simpa [T, entryCoords, S, cellState] using h4
  have ht8 : T 8 = 0 := by simpa [T, entryCoords, S, cellState] using h8
  have ht9 : T 9 = 0 := by simpa [T, entryCoords, S, cellState] using h9
  have ht14 : T 14 = 0 := by simpa [T, entryCoords] using hs14
  have ht15 : T 15 = 0 := by simpa [T, entryCoords] using hs15
  have htv : T 3 < T 0 := by simpa [T, entryCoords, S, cellState] using hv
  have htlen : data.length = T 0 * T 0 := by simpa [T, entryCoords, S, cellState] using hlen
  let P := rawPositiveCount (T 0) data f.val (T 3) (T 1) (T 2)
  let M := rawNegativeCount (T 0) f.val (T 3) (T 1) (T 2)
  have hcounts : P+M ≤ 3*S 0+2 := by
    have h := rawCounts_le (T 0) data f.val (T 3) (T 1) (T 2)
    simpa [P, M, T, entryCoords] using h
  have hcoeff : ∃ n, RegExec data (colorFamily f) T (putCounts T P M) n ∧
      n ≤ 1000000*(regSize T+2)^4 := by
    simpa [putCounts, P, M] using colorFamily_exec data T f htv htlen ht4 ht9 ht8 ht14 ht15
  obtain ⟨steps, he, hb⟩ := matrixEntry_exec C data (colorFamily f) S P M
    (1000000*(regSize T+2)^4) hs1 hs2 hs14 hs15 hcounts hcoeff tail
  have hout : TensorNP.Eigen.encRat ((P : ℚ) - (M : ℚ)) =
      colorEntryWord (R 0) data f.val (R 3) row col := by
    simp [colorEntryWord, P, M, T, entryCoords, S, cellState]
  refine ⟨steps, ?_, ?_⟩
  · simpa only [hout, S] using he
  · have hs : regSize S ≤ regSize R+row+col := by
      dsimp [S, cellState]
      have h := regSize_update_le (Function.update R 12 row) 13 col
      have h' := regSize_update_le R 12 row
      omega
    have ht : regSize T ≤ regSize S+row+col := by
      dsimp [T, entryCoords]
      have h := regSize_update_le (Function.update S 1 (S 12)) 2 (S 13)
      have h' := regSize_update_le S 1 (S 12)
      have h12 : S 12 = row := by simp [S, cellState]
      have h13 : S 13 = col := by simp [S, cellState]
      omega
    let X := regSize R+N+2
    have hx : 1 ≤ X := by dsimp [X]; omega
    have hs' : regSize S+2 ≤ 2*X := by dsimp [X]; omega
    have ht' : regSize T+2 ≤ 4*X := by dsimp [X]; omega
    have hsq : (regSize S+2)^2 ≤ 4*X^2 := by
      calc
        _ ≤ (2*X)^2 := Nat.pow_le_pow_left hs' 2
        _ = _ := by ring
    have hfour : (regSize T+2)^4 ≤ 256*X^4 := by
      calc
        _ ≤ (4*X)^4 := Nat.pow_le_pow_left ht' 4
        _ = _ := by ring
    have hp : X^2 ≤ X^4 := pow_le_pow_right₀ hx (by omega)
    have hmul := Nat.mul_le_mul_left (16*C+1000000) (hsq.trans (Nat.mul_le_mul_left 4 hp))
    have hmul' := Nat.mul_le_mul_left 1000000 hfour
    have ha : 1000000*(regSize T+2)^4 ≤ 256000000*X^4 := by
      calc
        _ ≤ 1000000*(256*X^4) := hmul'
        _ = _ := by ring
    have hb' : (16*C+1000000)*(regSize S+2)^2 ≤ (64*C+4000000)*X^4 := by
      calc
        _ ≤ (16*C+1000000)*(4*X^4) := hmul
        _ = _ := by ring
    have hc' : 256000000*X^4+(64*C+4000000)*X^4 ≤
        10000000000*(C+1)*X^4 := by
      calc
        _ = (256000000+(64*C+4000000))*X^4 := by ring
        _ ≤ (10000000000*(C+1))*X^4 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
    change steps ≤ 10000000000*(C+1)*X^4
    omega

theorem colorMatrix_exec (C : ℕ) (data : List BSym) (R : RegFile) (N : ℕ) (f : Fin 4)
    (hlen : data.length = R 0 * R 0) (hv : R 3 < R 0)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h4 : R 4 = 0) (h8 : R 8 = 0)
    (h9 : R 9 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0)
    (h6 : R 6 = N) (h12 : R 12 = 0) (h13 : R 13 = 0) (tail : List BSym) :
    ∃ steps, OutputExec C data (matrixProgram (matrixEntry (colorFamily f))) R tail R
      (matrixChunk (colorEntryWord (R 0) data f.val (R 3)) N N ++ tail) steps ∧
      steps ≤ regCharge R+1+(N*(100*(regSize R+N+1) +
        N*(10000000000*(C+1)*(regSize R+N+2)^4+5)+7)+1) := by
  have hQ : ∀ row, row < N → regCharge (cellState R row 0) ≤
      100*(regSize R+N+1) := by
    intro row hr
    have hs : regSize (cellState R row 0) ≤ regSize R+row := by
      have h := regSize_update_le (Function.update R 12 row) 13 0
      have h' := regSize_update_le R 12 row
      dsimp [cellState]
      omega
    simp only [regCharge]
    omega
  exact matrixProgram_exec C data _ _ R N _ _ h6 h12 h13
    (colorEntry_spec C data R N f hlen hv h1 h2 h4 h8 h9 h14 h15) hQ tail

end TensorNP.BilinearEncoder
end


/- Inlined module: ColorPass -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def colorMatrixBound (C S N : ℕ) : ℕ :=
  100*(S+1)+1+(N*(100*(S+N+1)+N*(10000000000*(C+1)*(S+N+2)^4+5)+7)+1)

theorem colorMatrixBound_mono (C N : ℕ) {S T : ℕ} (h : S ≤ T) :
    colorMatrixBound C S N ≤ colorMatrixBound C T N := by
  unfold colorMatrixBound
  gcongr

def colorOneBody (f : Fin 4) : OutputCmd :=
  .seq (matrixProgram (matrixEntry (colorFamily f))) (.reg (.inc 10))

def colorOne (f : Fin 4) : OutputCmd :=
  .seq (.reg (.assign 3 0)) (.down 3 (colorOneBody f))

def colorWord (v N : ℕ) (data : List BSym) (f : Fin 4) (i : ℕ) : List BSym :=
  sliceValueWord none N (colorValue v data f.val i)

private theorem scanCount_one (n : ℕ) : scanCount (fun _ => 1) n = n := by
  simp [scanCount]

theorem colorVertexLoop_exec (C : ℕ) (data : List BSym) (R : RegFile) (f : Fin 4)
    (v N cap count L : ℕ) (h0 : R 0 = v) (hlen : data.length = v*v)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h4 : R 4 = 0) (h8 : R 8 = 0) (h9 : R 9 = 0)
    (h12 : R 12 = 0) (h13 : R 13 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) (h6 : R 6 = N)
    (hc : count ≤ v) (hcap : L+count ≤ cap) (tail : List BSym) :
    let S := regSize R+v+cap
    let Q := 100*(S+1)
    let M := colorMatrixBound C S N
    ∃ steps, OutputExec C data (.down 3 (colorOneBody f)) (vertexScanState R count L) tail
      (vertexScanState R 0 (L+count)) (scanChunk (colorWord v N data f) count ++ tail) steps ∧
      steps ≤ count*(M+Q+6)+1 := by
  dsimp only
  let S := regSize R+v+cap
  let Q := 100*(S+1)
  let M := colorMatrixBound C S N
  have hbody : ∀ i L' tail', i < v → L'+1 ≤ cap → ∃ n,
      OutputExec C data (colorOneBody f) (vertexScanState R i L') tail'
        (vertexScanState R i (L'+1)) (colorWord v N data f i ++ tail') n ∧ n ≤ M+Q+1 := by
    intro i L' tail' hi hL
    let T := vertexScanState R i L'
    have h0' : T 0 = v := by simpa [T, vertexScanState] using h0
    have h3' : T 3 = i := by simp [T]
    have hlen' : data.length = T 0*T 0 := by simpa [h0'] using hlen
    have h1' : T 1 = 0 := by simpa [T, vertexScanState] using h1
    have h2' : T 2 = 0 := by simpa [T, vertexScanState] using h2
    have h4' : T 4 = 0 := by simpa [T, vertexScanState] using h4
    have h8' : T 8 = 0 := by simpa [T, vertexScanState] using h8
    have h9' : T 9 = 0 := by simpa [T, vertexScanState] using h9
    have h12' : T 12 = 0 := by simpa [T, vertexScanState] using h12
    have h13' : T 13 = 0 := by simpa [T, vertexScanState] using h13
    have h14' : T 14 = 0 := by simpa [T, vertexScanState] using h14
    have h15' : T 15 = 0 := by simpa [T, vertexScanState] using h15
    have h6' : T 6 = N := by simpa [T, vertexScanState] using h6
    obtain ⟨n, he, hn⟩ := colorMatrix_exec C data T N f hlen' (by omega)
      h1' h2' h4' h8' h9' h14' h15' h6' h12' h13' tail'
    have hword : colorEntryWord v data f.val i =
        (fun row col => TensorNP.Eigen.encRat (colorValue v data f.val i row col)) := rfl
    have he' : OutputExec C data (matrixProgram (matrixEntry (colorFamily f))) T tail' T
        (colorWord v N data f i ++ tail') n := by
      simpa only [h0', h3', colorWord, sliceValueWord, matrixValueWord, hword] using he
    have hinc := OutputExec.reg (C := C) (colorWord v N data f i ++ tail')
      (RegExec.inc (data := data) T 10)
    have hex := OutputExec.seq he' hinc
    refine ⟨n + 1 + regCharge T, ?_, ?_⟩
    · simpa only [colorOneBody, T, vertexScanState_inc10] using hex
    · have hs : regSize T ≤ S := by
        have hs' := vertexScanState_size R i L'
        dsimp [T, S] at *
        omega
      have hcharge : regCharge T ≤ Q := by dsimp [Q, regCharge]; omega
      have hlin : 100*(regSize T+N+1) ≤ 100*(S+N+1) := by omega
      have hp : (regSize T+N+2)^4 ≤ (S+N+2)^4 := Nat.pow_le_pow_left (by omega) 4
      have hm := Nat.mul_le_mul_left (10000000000*(C+1)) hp
      have hinner : 10000000000*(C+1)*(regSize T+N+2)^4+5 ≤
          10000000000*(C+1)*(S+N+2)^4+5 := by omega
      have hrow := Nat.mul_le_mul_left N hinner
      have hsum : 100*(regSize T+N+1)+N*(10000000000*(C+1)*(regSize T+N+2)^4+5)+7 ≤
          100*(S+N+1)+N*(10000000000*(C+1)*(S+N+2)^4+5)+7 := by omega
      have hout := Nat.mul_le_mul_left N hsum
      dsimp [M, colorMatrixBound]
      omega
  have hcap' : L + scanCount (fun _ => 1) count ≤ cap := by simpa only [scanCount_one] using hcap
  have he := sliceScan_exec C data (colorOneBody f) 3 (fun i L' => vertexScanState R i L')
    (colorWord v N data f) (fun _ => 1) v (M+Q+1) cap
    (fun i L' => vertexScanState_at3 R i L')
    (fun i L' => vertexScanState_down3 R i L') hbody count hc L hcap' tail
  simpa only [scanCount_one, S, Q, M] using he

theorem colorOne_exec (C : ℕ) (data : List BSym) (R : RegFile) (f : Fin 4)
    (v N cap : ℕ) (h0 : R 0 = v) (hlen : data.length = v*v)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h3 : R 3 = 0) (h4 : R 4 = 0) (h8 : R 8 = 0) (h9 : R 9 = 0)
    (h12 : R 12 = 0) (h13 : R 13 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) (h6 : R 6 = N)
    (hcap : R 10+v ≤ cap) (tail : List BSym) :
    let S := regSize R+v+cap
    let Q := 100*(S+1)
    let M := colorMatrixBound C S N
    ∃ steps, OutputExec C data (colorOne f) R tail
      (Function.update R 10 (R 10+v)) (scanChunk (colorWord v N data f) v ++ tail) steps ∧
      steps ≤ regCharge R+1+v*(M+Q+6)+1 := by
  dsimp only
  have hstart : Function.update R 3 (R 0) = vertexScanState R v (R 10) := by
    funext k
    by_cases hk3 : k = 3 <;> by_cases hk10 : k = 10 <;>
      simp [vertexScanState, Function.update, hk3, hk10, h0]
  have hend : vertexScanState R 0 (R 10+v) = Function.update R 10 (R 10+v) := by
    funext k
    by_cases hk3 : k = 3 <;> by_cases hk10 : k = 10 <;>
      simp [vertexScanState, Function.update, hk3, hk10, h3]
  have hassign := OutputExec.reg (C := C) tail (RegExec.assign (data := data) R 3 0)
  rw [hstart] at hassign
  obtain ⟨n, he, hn⟩ := colorVertexLoop_exec C data R f v N cap v (R 10) h0 hlen
    h1 h2 h4 h8 h9 h12 h13 h14 h15 h6 le_rfl hcap tail
  rw [hend] at he
  have hex := OutputExec.seq hassign he
  refine ⟨_, hex, ?_⟩
  omega


private theorem colorOne_frame_exec (C : ℕ) (data : List BSym) (R : RegFile) (f : Fin 4)
    (v N cap t : ℕ) (h0 : R 0 = v) (hlen : data.length = v*v)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h3 : R 3 = 0) (h4 : R 4 = 0) (h8 : R 8 = 0) (h9 : R 9 = 0)
    (h12 : R 12 = 0) (h13 : R 13 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) (h6 : R 6 = N)
    (hcap : t+v ≤ cap) (tail : List BSym) :
    let S := regSize R+v+2*cap
    let Q := 100*(S+1)
    let M := colorMatrixBound C S N
    let P := Q+1+v*(M+Q+6)+1
    ∃ steps, OutputExec C data (colorOne f) (Function.update R 10 t) tail
      (Function.update R 10 (t+v)) (scanChunk (colorWord v N data f) v ++ tail) steps ∧ steps ≤ P := by
  dsimp only
  let T := Function.update R 10 t
  have h0' : T 0 = v := by simpa [T] using h0
  have h1' : T 1 = 0 := by simpa [T] using h1
  have h2' : T 2 = 0 := by simpa [T] using h2
  have h3' : T 3 = 0 := by simpa [T] using h3
  have h4' : T 4 = 0 := by simpa [T] using h4
  have h8' : T 8 = 0 := by simpa [T] using h8
  have h9' : T 9 = 0 := by simpa [T] using h9
  have h12' : T 12 = 0 := by simpa [T] using h12
  have h13' : T 13 = 0 := by simpa [T] using h13
  have h14' : T 14 = 0 := by simpa [T] using h14
  have h15' : T 15 = 0 := by simpa [T] using h15
  have h6' : T 6 = N := by simpa [T] using h6
  have hcap' : T 10+v ≤ cap := by simpa [T] using hcap
  obtain ⟨n, he, hn⟩ := colorOne_exec C data T f v N cap h0' hlen h1' h2' h3' h4' h8' h9'
    h12' h13' h14' h15' h6' hcap' tail
  have he' : OutputExec C data (colorOne f) (Function.update R 10 t) tail
      (Function.update R 10 (t+v)) (scanChunk (colorWord v N data f) v ++ tail) n := by
    simpa [T] using he
  refine ⟨n, he', ?_⟩
  let S := regSize R+v+2*cap
  let Q := 100*(S+1)
  let M := colorMatrixBound C S N
  have ht : t ≤ cap := by omega
  have hsize : regSize T ≤ regSize R+cap := by
    have h := regSize_update_le R 10 t
    change regSize T ≤ regSize R+t at h
    omega
  have hS : regSize T+v+cap ≤ S := by dsimp [S]; omega
  have hQ : regCharge T ≤ Q := by dsimp [regCharge, Q]; omega
  have hm := colorMatrixBound_mono C N hS
  have hq : 100*(regSize T+v+cap+1) ≤ Q := by dsimp [Q]; omega
  have hsum : colorMatrixBound C (regSize T+v+cap) N +
      100*(regSize T+v+cap+1)+6 ≤ M+Q+6 := by dsimp [M]; omega
  have hmul := Nat.mul_le_mul_left v hsum
  dsimp [S, Q, M] at *
  omega


def colorPass : OutputCmd :=
  .seq (colorOne 3) (.seq (colorOne 2) (.seq (colorOne 1) (colorOne 0)))

def colorPassWord (v N : ℕ) (data : List BSym) : List BSym :=
  scanChunk (colorWord v N data 0) v ++ scanChunk (colorWord v N data 1) v ++
    scanChunk (colorWord v N data 2) v ++ scanChunk (colorWord v N data 3) v

theorem colorPass_exec (C : ℕ) (data : List BSym) (R : RegFile)
    (v N cap : ℕ) (h0 : R 0 = v) (hlen : data.length = v*v)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h3 : R 3 = 0) (h4 : R 4 = 0) (h8 : R 8 = 0) (h9 : R 9 = 0)
    (h12 : R 12 = 0) (h13 : R 13 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) (h6 : R 6 = N)
    (hcap : R 10+4*v ≤ cap) (tail : List BSym) :
    let S := regSize R+v+2*cap
    let Q := 100*(S+1)
    let M := colorMatrixBound C S N
    let P := Q+1+v*(M+Q+6)+1
    ∃ steps, OutputExec C data colorPass R tail (Function.update R 10 (R 10+4*v))
      (colorPassWord v N data ++ tail) steps ∧ steps ≤ 4*P+3 := by
  dsimp only
  let W3 := scanChunk (colorWord v N data 3) v
  let W2 := scanChunk (colorWord v N data 2) v
  let W1 := scanChunk (colorWord v N data 1) v
  let W0 := scanChunk (colorWord v N data 0) v
  obtain ⟨n3, he3, hb3⟩ := colorOne_frame_exec C data R 3 v N cap (R 10) h0 hlen
    h1 h2 h3 h4 h8 h9 h12 h13 h14 h15 h6 (by omega) tail
  obtain ⟨n2, he2, hb2⟩ := colorOne_frame_exec C data R 2 v N cap (R 10+v) h0 hlen
    h1 h2 h3 h4 h8 h9 h12 h13 h14 h15 h6 (by omega) (W3 ++ tail)
  obtain ⟨n1, he1, hb1⟩ := colorOne_frame_exec C data R 1 v N cap (R 10+v+v) h0 hlen
    h1 h2 h3 h4 h8 h9 h12 h13 h14 h15 h6 (by omega) (W2 ++ (W3 ++ tail))
  obtain ⟨n0, he0, hb0⟩ := colorOne_frame_exec C data R 0 v N cap (R 10+v+v+v) h0 hlen
    h1 h2 h3 h4 h8 h9 h12 h13 h14 h15 h6 (by omega) (W1 ++ (W2 ++ (W3 ++ tail)))
  have hstart : Function.update R 10 (R 10) = R := reg_update_self R 10
  rw [hstart] at he3
  have hfinal : R 10+v+v+v+v = R 10+4*v := by omega
  rw [hfinal] at he0
  have hex := OutputExec.seq he3 (OutputExec.seq he2 (OutputExec.seq he1 he0))
  refine ⟨n3+1+(n2+1+(n1+1+n0)), ?_, ?_⟩
  · simpa only [colorPass, colorPassWord, W0, W1, W2, W3, List.append_assoc] using hex
  · omega

end TensorNP.BilinearEncoder
end


/- Inlined module: FilteredScan -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

/-- Emit a selected minor slice and count it in the dimension header. -/
def countedSelect (emitter : OutputCmd) : OutputCmd :=
  .branch true 18 19 (.seq emitter (.reg (.inc 10))) (.reg .skip)

theorem countedSelect_true_exec (C : ℕ) (data : List BSym) (emitter : OutputCmd)
    (R : RegFile) (E tail : List BSym) (M : ℕ) (hlt : R 18 < R 19)
    (hem : ∃ n, OutputExec C data emitter R tail R (E ++ tail) n ∧ n ≤ M) :
    ∃ n, OutputExec C data (countedSelect emitter) R tail
      (Function.update R 10 (R 10 + 1)) (E ++ tail) n ∧
      n ≤ M + 2 * regCharge R + 1 := by
  obtain ⟨m, hm, hmb⟩ := hem
  have hi := OutputExec.reg (C := C) (E ++ tail) (RegExec.inc (data := data) R 10)
  have he := OutputExec.branch (C := C) (data := data) (R := R)
    (less := true) (r := 18) (s := 19)
    (yes := .seq emitter (.reg (.inc 10))) (no := .reg .skip)
    (by simpa [regCompare, hlt] using (OutputExec.seq hm hi))
  exact ⟨_, he, by omega⟩

-- The rejected-candidate case is a separate, routine completion obligation.
theorem countedSelect_false_exec (C : ℕ) (data : List BSym) (emitter : OutputCmd)
    (R : RegFile) (tail : List BSym) (hlt : ¬ R 18 < R 19) :
    ∃ n, OutputExec C data (countedSelect emitter) R tail R tail n ∧
      n ≤ regCharge R + 1 := by
  have hs := OutputExec.reg (C := C) tail (RegExec.skip (data := data) R)
  have he := OutputExec.branch (C := C) (data := data) (R := R)
    (less := true) (r := 18) (s := 19)
    (yes := .seq emitter (.reg (.inc 10))) (no := .reg .skip)
    (by simpa [regCompare, hlt] using hs)
  exact ⟨_, he, by omega⟩


theorem filteredScan_exec (C : ℕ) (data : List BSym) (emitter : OutputCmd)
    (state : ℕ → ℕ → RegFile) (E : ℕ → List BSym) (a N M Q cap : ℕ)
    (hleft : ∀ i L, state i L 18 = a)
    (hright : ∀ i L, state i L 19 = i)
    (hdown : ∀ i L, Function.update (state (i+1) L) 19 (state (i+1) L 19 - 1) = state i L)
    (hinc : ∀ i L, Function.update (state i L) 10 (state i L 10 + 1) = state i (L+1))
    (hcharge : ∀ i L, i < N → L ≤ cap → regCharge (state i L) ≤ Q)
    (hmat : ∀ i L tail, i < N → L+1 ≤ cap → ∃ n,
      OutputExec C data emitter (state i L) tail (state i L) (E i ++ tail) n ∧ n ≤ M)
    (count : ℕ) (hc : count ≤ N) (L : ℕ)
    (hcap : L + scanCount (fun i => if a < i then 1 else 0) count ≤ cap)
    (tail : List BSym) :
    ∃ steps, OutputExec C data (.down 19 (countedSelect emitter)) (state count L) tail
      (state 0 (L + scanCount (fun i => if a < i then 1 else 0) count))
      (scanChunk (fun i => if a < i then E i else []) count ++ tail) steps ∧
      steps ≤ count * (M + 2*Q + 7) + 1 := by
  let inc : ℕ → ℕ := fun i => if a < i then 1 else 0
  let word : ℕ → List BSym := fun i => if a < i then E i else []
  have hbody : ∀ i L tail, i < N → L + inc i ≤ cap → ∃ n,
      OutputExec C data (countedSelect emitter) (state i L) tail
        (state i (L + inc i)) (word i ++ tail) n ∧ n ≤ M + 2*Q + 2 := by
    intro i L' tail' hi hlocal
    have hL : L' ≤ cap := by omega
    have hQ := hcharge i L' hi hL
    by_cases h : a < i
    · have hlt : state i L' 18 < state i L' 19 := by simpa only [hleft, hright] using h
      have hmat' : L'+1 ≤ cap := by simpa [inc, h] using hlocal
      obtain ⟨n, he, hn⟩ := countedSelect_true_exec C data emitter (state i L')
        (E i) tail' M hlt (hmat i L' tail' hi hmat')
      refine ⟨n, ?_, ?_⟩
      · simpa only [inc, word, if_pos h, hinc i L'] using he
      · omega
    · have hlt : ¬ state i L' 18 < state i L' 19 := by simpa only [hleft, hright] using h
      obtain ⟨n, he, hn⟩ := countedSelect_false_exec C data emitter (state i L') tail' hlt
      refine ⟨n, ?_, ?_⟩
      · simpa only [inc, word, if_neg h, Nat.add_zero, List.nil_append] using he
      · omega
  have he := sliceScan_exec C data (countedSelect emitter) 19 state word inc N
    (M + 2*Q + 2) cap hright hdown hbody count hc L hcap tail
  simpa only [inc, word] using he

end TensorNP.BilinearEncoder
end


/- Inlined module: MinorCoefficient -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def minorPositive (R : RegFile) : ℕ :=
  naturalMonomial (R 18) (R 19) (R 1) (R 2)
def minorNegative (R : RegFile) : ℕ :=
  naturalMonomial (R 19) (R 18) (R 1) (R 2)
def minorAfter (R : RegFile) : RegFile := Function.update R 14 (minorPositive R)
def minorProgram : RegCmd := .seq (monoInc 14 18 19) (monoInc 15 19 18)

lemma minorPositive_le (R : RegFile) : minorPositive R ≤ 1 := by
  simp [minorPositive, naturalMonomial]
  split <;> omega

/-- The antisymmetric minor uses one positive and one negative unit entry. -/
theorem minorProgram_exec (data : List BSym) (R : RegFile)
    (h14 : R 14 = 0) (h15 : R 15 = 0) :
    ∃ n, RegExec data minorProgram R (putCounts R (minorPositive R) (minorNegative R)) n ∧
      n ≤ 10000 * (regSize R + 1) := by
  obtain ⟨a, ha, haB⟩ := monoInc_exec data R 14 18 19
  have ha' : RegExec data (monoInc 14 18 19) R (minorAfter R) a := by
    simpa [minorAfter, minorPositive, h14] using ha
  obtain ⟨b, hb, hbB⟩ := monoInc_exec data (minorAfter R) 15 19 18
  have hb' : RegExec data (monoInc 15 19 18) (minorAfter R)
      (putCounts R (minorPositive R) (minorNegative R)) b := by
    simpa [minorAfter, minorNegative, putCounts, h15] using hb
  refine ⟨a + 1 + b, RegExec.seq ha' hb', ?_⟩
  have hs : regSize (minorAfter R) ≤ regSize R + 1 :=
    (regSize_update_le R 14 (minorPositive R)).trans
      (Nat.add_le_add_left (minorPositive_le R) _)
  simp only [regCharge] at haB hbB
  omega

lemma minorNegative_le (R : RegFile) : minorNegative R ≤ 1 := by
  simp [minorNegative, naturalMonomial]
  split <;> omega

theorem minor_emit (C : ℕ) (data : List BSym) (R : RegFile)
    (h14 : R 14 = 0) (h15 : R 15 = 0) (tail : List BSym) :
    ∃ n, OutputExec C data (coeffEmit minorProgram) R tail R
      (TensorNP.Eigen.encRat ((minorPositive R : ℚ) - (minorNegative R : ℚ)) ++ tail) n ∧
      n ≤ 10000 * (regSize R + 1) + 1 + 16 * C := by
  obtain ⟨n, hn, hnb⟩ := minorProgram_exec data R h14 h15
  have hs : (minorPositive R + minorNegative R + 2)^2 ≤ 16 := by
    nlinarith [minorPositive_le R, minorNegative_le R]
  refine ⟨n + 1 + C * (minorPositive R + minorNegative R + 2)^2,
    emit_after_coeff hn h14 h15 tail, ?_⟩
  have hm := Nat.mul_le_mul_left C hs
  omega

end TensorNP.BilinearEncoder
end


/- Inlined module: MinorMatrix -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def minorEntryWord (a b row col : ℕ) : List BSym :=
  TensorNP.Eigen.encRat (((naturalMonomial a b row col : ℕ) : ℚ) -
    ((naturalMonomial b a row col : ℕ) : ℚ))

theorem minorEntry_spec (C : ℕ) (data : List BSym) (R : RegFile) (N : ℕ)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) :
    MatrixEntrySpec C data (matrixEntry minorProgram) (minorEntryWord (R 18) (R 19)) R N
      (100000000 * (C+1) * (regSize R+N+2)^2) := by
  intro row col tail hr hc
  let S := cellState R row col
  let T := entryCoords S
  have hs1 : S 1 = 0 := by simpa [S, cellState] using h1
  have hs2 : S 2 = 0 := by simpa [S, cellState] using h2
  have hs14 : S 14 = 0 := by simpa [S, cellState] using h14
  have hs15 : S 15 = 0 := by simpa [S, cellState] using h15
  have ht14 : T 14 = 0 := by simpa [T, entryCoords] using hs14
  have ht15 : T 15 = 0 := by simpa [T, entryCoords] using hs15
  have hcounts : minorPositive T + minorNegative T ≤ 3*S 0+2 := by
    have hp := minorPositive_le T
    have hm := minorNegative_le T
    omega
  have hcoeff := minorProgram_exec data T ht14 ht15
  obtain ⟨steps, he, hb⟩ := matrixEntry_exec C data minorProgram S
    (minorPositive T) (minorNegative T) (10000*(regSize T+1))
    hs1 hs2 hs14 hs15 hcounts hcoeff tail
  have hout : TensorNP.Eigen.encRat ((minorPositive T : ℚ) - (minorNegative T : ℚ)) =
      minorEntryWord (R 18) (R 19) row col := by
    simp [minorEntryWord, minorPositive, minorNegative, T, entryCoords, S, cellState]
  refine ⟨steps, ?_, ?_⟩
  · simpa only [hout, S] using he
  · have hs : regSize S ≤ regSize R+row+col := by
      dsimp [S, cellState]
      have h := regSize_update_le (Function.update R 12 row) 13 col
      have h' := regSize_update_le R 12 row
      omega
    have ht : regSize T ≤ regSize S+row+col := by
      dsimp [T, entryCoords]
      have h := regSize_update_le (Function.update S 1 (S 12)) 2 (S 13)
      have h' := regSize_update_le S 1 (S 12)
      have h12 : S 12 = row := by simp [S, cellState]
      have h13 : S 13 = col := by simp [S, cellState]
      omega
    let X := regSize R+N+2
    have hx : 1 ≤ X := by dsimp [X]; omega
    have hs' : regSize S+2 ≤ 2*X := by dsimp [X]; omega
    have ht' : regSize T+1 ≤ 5*X := by dsimp [X]; omega
    have hsq : (regSize S+2)^2 ≤ 4*X^2 := by
      calc
        _ ≤ (2*X)^2 := Nat.pow_le_pow_left hs' 2
        _ = _ := by ring
    have hbase : X ≤ X^2 := Nat.le_self_pow (by decide) _
    have hmul := Nat.mul_le_mul_left (16*C+1000000) hsq
    dsimp [X] at *
    nlinarith

theorem minorMatrix_exec (C : ℕ) (data : List BSym) (R : RegFile) (N : ℕ)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0)
    (h6 : R 6 = N) (h12 : R 12 = 0) (h13 : R 13 = 0) (tail : List BSym) :
    ∃ steps, OutputExec C data (matrixProgram (matrixEntry minorProgram)) R tail R
      (matrixChunk (minorEntryWord (R 18) (R 19)) N N ++ tail) steps ∧
      steps ≤ regCharge R+1+(N*((100*(regSize R+N+1)) +
        N*(100000000*(C+1)*(regSize R+N+2)^2+5)+7)+1) := by
  have hQ : ∀ row, row < N → regCharge (cellState R row 0) ≤
      100*(regSize R+N+1) := by
    intro row hr
    have hs : regSize (cellState R row 0) ≤ regSize R+row := by
      have h := regSize_update_le (Function.update R 12 row) 13 0
      have h' := regSize_update_le R 12 row
      dsimp [cellState]
      omega
    simp only [regCharge]
    omega
  exact matrixProgram_exec C data _ _ R N _ _ h6 h12 h13
    (minorEntry_spec C data R N h1 h2 h14 h15) hQ tail

end TensorNP.BilinearEncoder
end


/- Inlined module: MinorInner -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def minorInner : OutputCmd := .down 19 (countedSelect (matrixProgram (matrixEntry minorProgram)))

def minorMatrixBound (C S N : ℕ) : ℕ :=
  100*(S+1)+1+(N*(100*(S+N+1)+N*(100000000*(C+1)*(S+N+2)^2+5)+7)+1)

theorem minorInner_exec (C : ℕ) (data : List BSym) (R : RegFile)
    (a count L N cap : ℕ)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0)
    (h12 : R 12 = 0) (h13 : R 13 = 0) (h6 : R 6 = N)
    (hc : count ≤ N)
    (hcap : L + scanCount (fun i => if a < i then 1 else 0) count ≤ cap)
    (tail : List BSym) :
    ∃ steps, OutputExec C data minorInner (minorScanState R a count L) tail
      (minorScanState R a 0 (L + scanCount (fun i => if a < i then 1 else 0) count))
      (scanChunk (fun i => if a < i then matrixValueWord (minorValue a i) N else []) count ++ tail) steps ∧
      steps ≤ count * (minorMatrixBound C (regSize R + a + N + cap) N +
        2 * (100 * (regSize R + a + N + cap + 1)) + 7) + 1 := by
  let S := regSize R + a + N + cap
  let Q := 100*(S+1)
  let M := minorMatrixBound C S N
  have hcharge : ∀ i L', i < N → L' ≤ cap → regCharge (minorScanState R a i L') ≤ Q := by
    intro i L' hi hL
    have hs := minorScanState_size R a i L'
    dsimp [Q, S, regCharge]
    omega
  have hmat : ∀ i L' tail', i < N → L'+1 ≤ cap → ∃ n,
      OutputExec C data (matrixProgram (matrixEntry minorProgram)) (minorScanState R a i L') tail'
        (minorScanState R a i L') (matrixValueWord (minorValue a i) N ++ tail') n ∧ n ≤ M := by
    intro i L' tail' hi hL
    let T := minorScanState R a i L'
    have h1' : T 1 = 0 := by simpa [T, minorScanState] using h1
    have h2' : T 2 = 0 := by simpa [T, minorScanState] using h2
    have h14' : T 14 = 0 := by simpa [T, minorScanState] using h14
    have h15' : T 15 = 0 := by simpa [T, minorScanState] using h15
    have h12' : T 12 = 0 := by simpa [T, minorScanState] using h12
    have h13' : T 13 = 0 := by simpa [T, minorScanState] using h13
    have h6' : T 6 = N := by simpa [T, minorScanState] using h6
    obtain ⟨n, he, hb⟩ := minorMatrix_exec C data T N h1' h2' h14' h15' h6' h12' h13' tail'
    refine ⟨n, ?_, ?_⟩
    · have heq : minorEntryWord a i = (fun row col => TensorNP.Eigen.encRat (minorValue a i row col)) := rfl
      simpa only [T, minorScanState_at18, minorScanState_at19, matrixValueWord, heq] using he
    · have hs : regSize T ≤ S := by
        have hs' := minorScanState_size R a i L'
        dsimp [T, S] at *
        omega
      have hcharge' : regCharge T ≤ 100*(S+1) := by
        simp only [regCharge]
        omega
      have hlin : 100*(regSize T+N+1) ≤ 100*(S+N+1) := by omega
      have hp : (regSize T+N+2)^2 ≤ (S+N+2)^2 := Nat.pow_le_pow_left (by omega) 2
      have hm := Nat.mul_le_mul_left (100000000*(C+1)) hp
      have hinner : 100000000*(C+1)*(regSize T+N+2)^2+5 ≤
          100000000*(C+1)*(S+N+2)^2+5 := by omega
      have hrow := Nat.mul_le_mul_left N hinner
      have hsum : 100*(regSize T+N+1)+N*(100000000*(C+1)*(regSize T+N+2)^2+5)+7 ≤
          100*(S+N+1)+N*(100000000*(C+1)*(S+N+2)^2+5)+7 := by omega
      have hout := Nat.mul_le_mul_left N hsum
      dsimp [M, minorMatrixBound]
      omega
  have he := filteredScan_exec C data (matrixProgram (matrixEntry minorProgram))
    (fun i L' => minorScanState R a i L') (fun i => matrixValueWord (minorValue a i) N)
    a N M Q cap
    (fun i L' => minorScanState_at18 R a i L')
    (fun i L' => minorScanState_at19 R a i L')
    (fun i L' => minorScanState_down19 R a i L')
    (fun i L' => minorScanState_inc10 R a i L') hcharge hmat count hc L hcap tail
  simpa only [minorInner, S, Q, M] using he

end TensorNP.BilinearEncoder
end


/- Inlined module: MinorPass -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def minorOuterBody : OutputCmd := .seq (.reg (.assign 19 7)) minorInner

def minorOuter : OutputCmd := .down 18 minorOuterBody

def minorInc (N a : ℕ) : ℕ := scanCount (fun b => if a < b then 1 else 0) N

def minorWord (N a : ℕ) : List BSym :=
  scanChunk (fun b => if a < b then matrixValueWord (minorValue a b) N else []) N

theorem minorMatrixBound_mono (C N : ℕ) {S T : ℕ} (h : S ≤ T) :
    minorMatrixBound C S N ≤ minorMatrixBound C T N := by
  unfold minorMatrixBound
  gcongr

theorem minorOuter_exec (C : ℕ) (data : List BSym) (R : RegFile) (N cap count L : ℕ)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0)
    (h12 : R 12 = 0) (h13 : R 13 = 0) (h6 : R 6 = N) (h7 : R 7 = N)
    (hc : count ≤ N) (hcap : L + scanCount (minorInc N) count ≤ cap) (tail : List BSym) :
    let S := regSize R + 2*N + cap
    let Q := 100*(S+1)
    let M := minorMatrixBound C S N
    let B := Q + N*(M+2*Q+7)+2
    ∃ steps, OutputExec C data minorOuter (minorScanState R count 0 L) tail
      (minorScanState R 0 0 (L + scanCount (minorInc N) count))
      (scanChunk (minorWord N) count ++ tail) steps ∧ steps ≤ count*(B+5)+1 := by
  dsimp only
  let S := regSize R + 2*N + cap
  let Q := 100*(S+1)
  let M := minorMatrixBound C S N
  let B := Q + N*(M+2*Q+7)+2
  have hbody : ∀ a L' tail', a < N → L' + minorInc N a ≤ cap → ∃ n,
      OutputExec C data minorOuterBody (minorScanState R a 0 L') tail'
        (minorScanState R a 0 (L'+minorInc N a)) (minorWord N a ++ tail') n ∧ n ≤ B := by
    intro a L' tail' ha hlocal
    let T := minorScanState R a 0 L'
    have hassign : OutputExec C data (.reg (.assign 19 7)) T tail'
        (minorScanState R a N L') tail' (regCharge T) := by
      have he := OutputExec.reg (C := C) tail' (RegExec.assign (data := data) T 19 7)
      simpa only [T, minorScanState_set19_from7_eq R a 0 L' N h7] using he
    obtain ⟨n, he, hn⟩ := minorInner_exec C data R a N L' N cap h1 h2 h14 h15 h12 h13 h6
      le_rfl hlocal tail'
    have he' : OutputExec C data minorInner (minorScanState R a N L') tail'
        (minorScanState R a 0 (L'+minorInc N a)) (minorWord N a ++ tail') n := by
      simpa only [minorInc, minorWord] using he
    have hex := OutputExec.seq hassign he'
    refine ⟨_, hex, ?_⟩
    have hL : L' ≤ cap := by omega
    have hS : regSize T ≤ S := by
      have hs := minorScanState_size R a 0 L'
      dsimp [T, S] at *
      omega
    have hQ : regCharge T ≤ Q := by dsimp [regCharge, Q]; omega
    have haS : regSize R + a + N + cap ≤ S := by dsimp [S]; omega
    have hm := minorMatrixBound_mono C N haS
    have hq : 100*(regSize R + a + N + cap + 1) ≤ Q := by dsimp [Q]; omega
    have hinner : minorMatrixBound C (regSize R + a + N + cap) N +
        2*(100*(regSize R + a + N + cap + 1))+7 ≤ M+2*Q+7 := by dsimp [M]; omega
    have hmul := Nat.mul_le_mul_left N hinner
    dsimp [B]
    omega
  have he := sliceScan_exec C data minorOuterBody 18 (fun a L' => minorScanState R a 0 L')
    (minorWord N) (minorInc N) N B cap
    (fun a L' => minorScanState_at18 R a 0 L')
    (fun a L' => minorScanState_down18 R a 0 L') hbody count hc L hcap tail
  simpa only [minorOuter, S, Q, M, B] using he


def minorPass : OutputCmd := .seq (.reg (.assign 18 7)) minorOuter

theorem minorPass_exec (C : ℕ) (data : List BSym) (R : RegFile) (N cap : ℕ)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0)
    (h12 : R 12 = 0) (h13 : R 13 = 0) (h6 : R 6 = N) (h7 : R 7 = N)
    (h18 : R 18 = 0) (h19 : R 19 = 0)
    (hcap : R 10 + scanCount (minorInc N) N ≤ cap) (tail : List BSym) :
    let S := regSize R + 2*N + cap
    let Q := 100*(S+1)
    let M := minorMatrixBound C S N
    let B := Q + N*(M+2*Q+7)+2
    ∃ steps, OutputExec C data minorPass R tail
      (Function.update R 10 (R 10 + scanCount (minorInc N) N))
      (scanChunk (minorWord N) N ++ tail) steps ∧
      steps ≤ regCharge R + 1 + N*(B+5) + 1 := by
  dsimp only
  have hstart : Function.update R 18 (R 7) = minorScanState R N 0 (R 10) := by
    funext k
    by_cases hk18 : k = 18 <;> by_cases hk19 : k = 19 <;> by_cases hk10 : k = 10 <;>
      simp [minorScanState, Function.update, hk18, hk19, hk10, h7, h19]
  have hend : minorScanState R 0 0 (R 10 + scanCount (minorInc N) N) =
      Function.update R 10 (R 10 + scanCount (minorInc N) N) := by
    funext k
    by_cases hk18 : k = 18 <;> by_cases hk19 : k = 19 <;> by_cases hk10 : k = 10 <;>
      simp [minorScanState, Function.update, hk18, hk19, hk10, h18, h19]
  have hassign := OutputExec.reg (C := C) tail (RegExec.assign (data := data) R 18 7)
  rw [hstart] at hassign
  obtain ⟨n, he, hn⟩ := minorOuter_exec C data R N cap N (R 10) h1 h2 h14 h15 h12 h13 h6 h7
    le_rfl hcap tail
  rw [hend] at he
  have hex := OutputExec.seq hassign he
  refine ⟨_, hex, ?_⟩
  omega

end TensorNP.BilinearEncoder
end


/- Inlined module: ComplexPass -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def complexPass : OutputCmd := .seq colorPass minorPass

theorem passWord_none_eq (v : ℕ) (data : List BSym) :
    passWord none v data = scanChunk (minorWord (2*v+1)) (2*v+1) ++ colorPassWord v (2*v+1) data := by
  have h4 (f : ℕ → List BSym) :
      (List.range 4).flatMap f = f 0 ++ f 1 ++ f 2 ++ f 3 := by
    simp [List.range_succ, List.append_assoc]
  simp only [passWord, scanChunk, colorPassWord, sliceValueWord, h4, List.append_assoc]
  rfl

theorem complexPass_exec (C : ℕ) (data : List BSym) (R : RegFile) (v N cap : ℕ)
    (h0 : R 0 = v) (hlen : data.length = v*v) (hN : N = 2*v+1)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h3 : R 3 = 0) (h4 : R 4 = 0) (h8 : R 8 = 0) (h9 : R 9 = 0)
    (h12 : R 12 = 0) (h13 : R 13 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0)
    (h18 : R 18 = 0) (h19 : R 19 = 0) (h6 : R 6 = N) (h7 : R 7 = N)
    (hcap : R 10+4*v+scanCount (minorInc N) N ≤ cap) (tail : List BSym) :
    let Sc := regSize R+v+2*cap
    let Qc := 100*(Sc+1)
    let Mc := colorMatrixBound C Sc N
    let P := Qc+1+v*(Mc+Qc+6)+1
    let S := regSize R+2*N+2*cap
    let Q := 100*(S+1)
    let M := minorMatrixBound C S N
    let B := Q+N*(M+2*Q+7)+2
    ∃ steps, OutputExec C data complexPass R tail
      (Function.update R 10 (R 10+4*v+scanCount (minorInc N) N))
      (passWord none v data ++ tail) steps ∧
      steps ≤ (4*P+3)+1+(Q+1+N*(B+5)+1) := by
  dsimp only
  let T := Function.update R 10 (R 10+4*v)
  obtain ⟨c, hec, hbc⟩ := colorPass_exec C data R v N cap h0 hlen
    h1 h2 h3 h4 h8 h9 h12 h13 h14 h15 h6 (by omega) tail
  have h1' : T 1 = 0 := by simpa [T] using h1
  have h2' : T 2 = 0 := by simpa [T] using h2
  have h12' : T 12 = 0 := by simpa [T] using h12
  have h13' : T 13 = 0 := by simpa [T] using h13
  have h14' : T 14 = 0 := by simpa [T] using h14
  have h15' : T 15 = 0 := by simpa [T] using h15
  have h18' : T 18 = 0 := by simpa [T] using h18
  have h19' : T 19 = 0 := by simpa [T] using h19
  have h6' : T 6 = N := by simpa [T] using h6
  have h7' : T 7 = N := by simpa [T] using h7
  have hcap' : T 10+scanCount (minorInc N) N ≤ cap := by simpa [T] using hcap
  obtain ⟨m, hem, hbm⟩ := minorPass_exec C data T N cap h1' h2' h14' h15' h12' h13' h6' h7'
    h18' h19' hcap' (colorPassWord v N data ++ tail)
  have hfinal : Function.update T 10 (T 10+scanCount (minorInc N) N) =
      Function.update R 10 (R 10+4*v+scanCount (minorInc N) N) := by simp [T]
  rw [hfinal] at hem
  have hex := OutputExec.seq hec hem
  refine ⟨c+1+m, ?_, ?_⟩
  · subst N
    simpa only [complexPass, passWord_none_eq, List.append_assoc] using hex
  · let S := regSize R+2*N+2*cap
    let Q := 100*(S+1)
    let M := minorMatrixBound C S N
    let B := Q+N*(M+2*Q+7)+2
    have hsize : regSize T ≤ regSize R+cap := by
      have h := regSize_update_le R 10 (R 10+4*v)
      change regSize T ≤ _ at h
      omega
    have hS : regSize T+2*N+cap ≤ S := by dsimp [S]; omega
    have hQ : regCharge T ≤ Q := by dsimp [Q, regCharge]; omega
    have hm := minorMatrixBound_mono C N hS
    have hq : 100*(regSize T+2*N+cap+1) ≤ Q := by dsimp [Q]; omega
    have hin : minorMatrixBound C (regSize T+2*N+cap) N +
        2*(100*(regSize T+2*N+cap+1))+7 ≤ M+2*Q+7 := by dsimp [M]; omega
    have hn := Nat.mul_le_mul_left N hin
    have hB : 100*(regSize T+2*N+cap+1) +
        N*(minorMatrixBound C (regSize T+2*N+cap) N + 2*(100*(regSize T+2*N+cap+1))+7)+2 ≤ B := by
      dsimp [B]
      omega
    have hNB := Nat.mul_le_mul_left N (Nat.add_le_add_right hB 5)
    dsimp [S, Q, M, B] at *
    omega

end TensorNP.BilinearEncoder
end


/- Inlined module: ComplexBudget -/
section
set_option autoImplicit false
open TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def complexPassBudget (C size v cap : ℕ) : ℕ :=
  let N := 2*v+1
  let Sc := size+v+2*cap
  let Qc := 100*(Sc+1)
  let Mc := colorMatrixBound C Sc N
  let P := Qc+1+v*(Mc+Qc+6)+1
  let S := size+2*N+2*cap
  let Q := 100*(S+1)
  let M := minorMatrixBound C S N
  let B := Q+N*(M+2*Q+7)+2
  (4*P+3)+1+(Q+1+N*(B+5)+1)

theorem complexPassBudget_le (C size v cap : ℕ)
    (hs : size ≤ 100*(v+1)^2) (hc : cap ≤ 100*(v+1)^2) :
    complexPassBudget C size v cap ≤ 10^35*(C+1)*(v+1)^16 := by
  let X := (v+1)^2
  have hsquare : v+1 ≤ (v+1)^2 := Nat.le_self_pow (by decide) _
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hv : v ≤ X := by dsimp [X]; omega
  have hmono : complexPassBudget C size v cap ≤ complexPassBudget C (100*X) X (100*X) := by
    dsimp [complexPassBudget, colorMatrixBound, minorMatrixBound]
    gcongr
  have hp (k : ℕ) (hk : k ≤ 8) : (C+1)*X^k ≤ (C+1)*X^8 :=
    Nat.mul_le_mul_left (C+1) (pow_le_pow_right₀ hx hk)
  have hz (k : ℕ) : X^k ≤ (C+1)*X^k := by
    simpa using Nat.mul_le_mul_right (X^k) (show 1 ≤ C+1 by omega)
  have hbound : complexPassBudget C (100*X) X (100*X) ≤ 10^35*(C+1)*X^8 := by
    have h0 := hp 0 (by omega)
    have h1 := hp 1 (by omega)
    have h2 := hp 2 (by omega)
    have h3 := hp 3 (by omega)
    have h4 := hp 4 (by omega)
    have h5 := hp 5 (by omega)
    have h6 := hp 6 (by omega)
    have h7 := hp 7 (by omega)
    have z0 := hz 0
    have z1 := hz 1
    have z2 := hz 2
    have z3 := hz 3
    have z4 := hz 4
    have z5 := hz 5
    have z6 := hz 6
    have z7 := hz 7
    dsimp [complexPassBudget, colorMatrixBound, minorMatrixBound]
    nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, z0, z1, z2, z3, z4, z5, z6, z7]
  calc
    _ ≤ complexPassBudget C (100*X) X (100*X) := hmono
    _ ≤ 10^35*(C+1)*X^8 := hbound
    _ = 10^35*(C+1)*(v+1)^16 := by dsimp [X]; ring

end TensorNP.BilinearEncoder
end


/- Inlined module: IndicatorScan -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

theorem scanCount_indicator (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    scanCount (fun i => if P i then 1 else 0) n =
      ((List.range n).filter (fun i => decide (P i))).length := by
  induction n with
  | zero => simp [scanCount]
  | succ n ih =>
    simp [scanCount, List.range_succ] at ih ⊢
    rw [ih]
    by_cases h : P n <;> simp [h]

theorem scanChunk_indicator (P : ℕ → Prop) [DecidablePred P] (E : ℕ → List BSym) (n : ℕ) :
    scanChunk (fun i => if P i then E i else []) n =
      ((List.range n).filter (fun i => decide (P i))).flatMap E := by
  induction n with
  | zero => simp [scanChunk]
  | succ n ih =>
    simp [scanChunk, List.range_succ, List.flatMap_append] at ih ⊢
    rw [ih]
    by_cases h : P n <;> simp [h]

end TensorNP.BilinearEncoder
end


/- Inlined module: CandidateWord -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Bilinear
namespace TensorNP.BilinearEncoder

def minorCandidates (N : ℕ) : List (Fin N × Fin N) :=
  List.ofFn (finProdFinEquiv.symm : Fin (N*N) → Fin N × Fin N)

def chooseMinor (N : ℕ) (ab : Fin N × Fin N) : Option (MinorIdx N) :=
  if h : ab.1 < ab.2 then some ⟨ab,h⟩ else none

private def selectedMinors (N : ℕ) : List (MinorIdx N) :=
  (minorCandidates N).filterMap (chooseMinor N)

private theorem selected_values (N : ℕ) (xs : List (Fin N × Fin N)) :
    (xs.filterMap (chooseMinor N)).map Subtype.val = xs.filter (fun ab ↦ decide (ab.1 < ab.2)) := by
  induction xs with
  | nil => rfl
  | cons ab xs ih =>
      by_cases h : ab.1 < ab.2 <;> simp [chooseMinor, h, ih]

private theorem selected_eq_enumeration (N count : ℕ) (e : Fin count ≃ MinorIdx N)
    (he : List.ofFn (fun k : Fin count ↦ (e k).val) =
      (minorCandidates N).filter (fun ab ↦ decide (ab.1 < ab.2))) :
    selectedMinors N = List.ofFn e := by
  apply (List.map_injective_iff.mpr Subtype.coe_injective)
  rw [selectedMinors, selected_values]
  simpa [List.map_ofFn, Function.comp_def] using he.symm

private theorem flatten_candidates {α : Type*} (N : ℕ) (xs : List (Fin N × Fin N))
    (word : MinorIdx N → List α) :
    (xs.map (fun ab ↦ (chooseMinor N ab).elim [] word)).flatten =
      ((xs.filterMap (chooseMinor N)).map word).flatten := by
  induction xs with
  | nil => rfl
  | cons ab xs ih =>
      cases h : chooseMinor N ab <;> simp [h, ih]

private theorem candidate_words_eq {α : Type*} (N count : ℕ) (e : Fin count ≃ MinorIdx N)
    (he : List.ofFn (fun k : Fin count ↦ (e k).val) =
      (minorCandidates N).filter (fun ab ↦ decide (ab.1 < ab.2)))
    (word : MinorIdx N → List α) :
    ((minorCandidates N).map (fun ab ↦ (chooseMinor N ab).elim [] word)).flatten =
      ((List.ofFn e).map word).flatten := by
  rw [flatten_candidates]
  change ((selectedMinors N).map word).flatten = _
  rw [selected_eq_enumeration N count e he]

theorem minorCandidate_word_eq (N : ℕ) (W : ℕ → ℕ → List BSym)
    (word : MinorIdx N → List BSym)
    (hword : ∀ ab, W ab.val.1.val ab.val.2.val = word ab) :
    (List.range N).flatMap (fun a => (List.range N).flatMap (fun b =>
      if a < b then W a b else [])) =
      (List.ofFn (fun i : Fin (N.choose 2) => word (minorEquiv N i))).flatten := by
  rw [squareWord_eq_ofFn]
  have hgrid : (List.ofFn (fun q : Fin (N*N) =>
      if (finProdFinEquiv.symm q).1.val < (finProdFinEquiv.symm q).2.val then
        W (finProdFinEquiv.symm q).1.val (finProdFinEquiv.symm q).2.val else [])).flatten =
      ((minorCandidates N).map (fun ab => (chooseMinor N ab).elim [] word)).flatten := by
    simp only [minorCandidates, List.map_ofFn, Function.comp_def]
    apply congrArg List.flatten
    congr 1
    funext q
    let ab := finProdFinEquiv.symm q
    change (if ab.1.val < ab.2.val then W ab.1.val ab.2.val else []) =
      (chooseMinor N ab).elim [] word
    by_cases h : ab.1 < ab.2
    · have hv : ab.1.val < ab.2.val := h
      simp only [chooseMinor, dif_pos h, if_pos hv, Option.elim_some]
      exact hword ⟨ab,h⟩
    · have hv : ¬ ab.1.val < ab.2.val := h
      simp only [chooseMinor, dif_neg h, if_neg hv, Option.elim_none]
  rw [hgrid]
  have he : List.ofFn (fun k : Fin (N.choose 2) => (minorEquiv N k).val) =
      (minorCandidates N).filter (fun ab => decide (ab.1 < ab.2)) := by
    simpa [minorPairs, minorCandidates] using minorEquiv_order N
  simpa only [List.map_ofFn, Function.comp_def] using
    (candidate_words_eq N (N.choose 2) (minorEquiv N) he word)

end TensorNP.BilinearEncoder
end


/- Inlined module: MinorCount -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Bilinear
namespace TensorNP.BilinearEncoder

private theorem scanChunk_length (E : ℕ → List BSym) (inc : ℕ → ℕ)
    (h : ∀ i, (E i).length = inc i) (n : ℕ) :
    (scanChunk E n).length = scanCount inc n := by
  simp [scanChunk, scanCount, List.length_flatMap, h]

theorem minorCount_eq (N : ℕ) : scanCount (minorInc N) N = N.choose 2 := by
  let E : ℕ → ℕ → List BSym := fun a b => if a < b then [BSym.zero] else []
  have hinner (a : ℕ) : ((List.range N).flatMap (E a)).length = minorInc N a := by
    change (scanChunk (E a) N).length = _
    apply scanChunk_length
    intro b
    simp only [E]
    split <;> rfl
  have hleft : ((List.range N).flatMap (fun a => (List.range N).flatMap (E a))).length =
      scanCount (minorInc N) N := by
    change (scanChunk (fun a => (List.range N).flatMap (E a)) N).length = _
    exact scanChunk_length _ _ hinner N
  have hw := minorCandidate_word_eq N (fun _ _ => [BSym.zero])
    (fun _ => [BSym.zero]) (fun _ => rfl)
  have hl := congrArg List.length hw
  change ((List.range N).flatMap (fun a => (List.range N).flatMap (E a))).length = _ at hl
  rw [hleft] at hl
  simpa [List.length_flatten, List.map_ofFn, Function.comp_def] using hl

theorem minorCount_le (N : ℕ) : scanCount (minorInc N) N ≤ N*N := by
  rw [minorCount_eq]
  have h := congrArg List.length (minorEquiv_order N)
  have hp := minorPairs_length_le N
  have heq : N.choose 2 = (minorPairs N).length := by simpa using h
  omega

theorem minorSliceCount (v : ℕ) :
    scanCount (minorInc (2*v+1)) (2*v+1) + 4*v = v*(2*v+5) := by
  rw [minorCount_eq, Nat.choose_two_right]
  have hsub : 2*v+1-1 = 2*v := by omega
  rw [hsub]
  have hmul : (2*v+1)*(2*v) = (v*(2*v+1))*2 := by ring
  rw [hmul, Nat.mul_div_cancel _ (by omega)]
  ring

end TensorNP.BilinearEncoder
end


/- Inlined module: ZeroNative -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def zeroMatrixInc : OutputCmd :=
  .seq (matrixProgram (matrixEntry minorProgram)) (.reg (.inc 10))

theorem zeroMatrixInc_exec (C : ℕ) (data : List BSym) (R : RegFile) (N : ℕ)
    (h18 : R 18 = 0) (h19 : R 19 = 0)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h12 : R 12 = 0) (h13 : R 13 = 0)
    (h14 : R 14 = 0) (h15 : R 15 = 0) (h6 : R 6 = N) (tail : List BSym) :
    ∃ steps, OutputExec C data zeroMatrixInc R tail (Function.update R 10 (R 10 + 1))
      (matrixValueWord (minorValue 0 0) N ++ tail) steps ∧
      steps ≤ minorMatrixBound C (regSize R) N + regCharge R + 1 := by
  obtain ⟨n, he, hb⟩ := minorMatrix_exec C data R N h1 h2 h14 h15 h6 h12 h13 tail
  have he' : OutputExec C data (matrixProgram (matrixEntry minorProgram)) R tail R
      (matrixValueWord (minorValue 0 0) N ++ tail) n := by
    have heq : minorEntryWord 0 0 = (fun row col => TensorNP.Eigen.encRat (minorValue 0 0 row col)) := rfl
    simpa only [h18, h19, matrixValueWord, heq] using he
  refine ⟨n + 1 + regCharge R, ?_, ?_⟩
  · exact OutputExec.seq he' (OutputExec.reg _ (RegExec.inc R 10))
  · simp only [minorMatrixBound, regCharge] at *
    omega

def zeroDouble : OutputCmd := .seq zeroMatrixInc zeroMatrixInc

theorem zeroDouble_exec (C : ℕ) (data : List BSym) (R : RegFile) (N : ℕ)
    (h18 : R 18 = 0) (h19 : R 19 = 0)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h12 : R 12 = 0) (h13 : R 13 = 0)
    (h14 : R 14 = 0) (h15 : R 15 = 0) (h6 : R 6 = N) (tail : List BSym) :
    ∃ steps, OutputExec C data zeroDouble R tail (Function.update R 10 (R 10 + 2))
      (matrixValueWord (minorValue 0 0) N ++ matrixValueWord (minorValue 0 0) N ++ tail) steps ∧
      steps ≤ 2 * (minorMatrixBound C (regSize R + R 10 + 2) N +
        100 * (regSize R + R 10 + 3) + 1) + 1 := by
  obtain ⟨n, hn, hnb⟩ := zeroMatrixInc_exec C data R N h18 h19 h1 h2 h12 h13 h14 h15 h6 tail
  let S := Function.update R 10 (R 10 + 1)
  obtain ⟨m, hm, hmb⟩ := zeroMatrixInc_exec C data S N
    (by simpa [S] using h18) (by simpa [S] using h19)
    (by simpa [S] using h1) (by simpa [S] using h2)
    (by simpa [S] using h12) (by simpa [S] using h13)
    (by simpa [S] using h14) (by simpa [S] using h15)
    (by simpa [S] using h6) (matrixValueWord (minorValue 0 0) N ++ tail)
  refine ⟨n + 1 + m, ?_, ?_⟩
  · simpa [zeroDouble, S, List.append_assoc, Nat.add_assoc] using OutputExec.seq hn hm
  · have hs : regSize S ≤ regSize R + R 10 + 1 := by
      simpa [S, Nat.add_assoc] using regSize_update_le R 10 (R 10 + 1)
    have hmono : ∀ x y : ℕ, x ≤ y → minorMatrixBound C x N ≤ minorMatrixBound C y N := by
      intro x y hxy
      simp only [minorMatrixBound]
      gcongr
    have hR := hmono (regSize R) (regSize R + R 10 + 2) (by omega)
    have hS := hmono (regSize S) (regSize R + R 10 + 2) (by omega)
    simp only [regCharge] at hnb hmb
    omega

end TensorNP.BilinearEncoder
end


/- Inlined module: ComplexEncoder -/
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def complexBody : OutputCmd :=
  .seq (.reg (dimensionInit false)) (.branch false 0 1 zeroMatrixInc complexPass)

def complexBodyRegs (v : ℕ) : RegFile :=
  Function.update (dimensionState false (encoderRegs v)) 10 (complexSlices v)

def complexBodyWord (v : ℕ) (data : List BSym) : List BSym :=
  if v = 0 then matrixValueWord (minorValue 0 0) 1 else passWord none v data

private theorem complexSlices_pos (v : ℕ) (hv : v ≠ 0) :
    complexSlices v = v*(2*v+5) := by
  cases v with
  | zero => contradiction
  | succ v => rfl

theorem complexBody_exec (C : ℕ) (data : List BSym) (v : ℕ)
    (hlen : data.length = v*v) :
    ∃ steps, OutputExec C data complexBody (encoderRegs v) [] (complexBodyRegs v)
      (complexBodyWord v data) steps ∧
      steps ≤ 10^40*(C+1)*(v+1)^16 := by
  let S := dimensionState false (encoderRegs v)
  have hs0 : S 0 = v := by simp [S, encoderRegs]
  have hs1 : S 1 = 0 := by simp [S, dimensionState, encoderRegs]
  have hs2 : S 2 = 0 := by simp [S, dimensionState, encoderRegs]
  have hs3 : S 3 = 0 := by simp [S, dimensionState, encoderRegs]
  have hs4 : S 4 = 0 := by simp [S, dimensionState, encoderRegs]
  have hs6 : S 6 = 2*v+1 := by simp [S, encoderRegs]
  have hs7 : S 7 = 2*v+1 := by simp [S, encoderRegs]
  have hs8 : S 8 = 0 := by simp [S, dimensionState, encoderRegs]
  have hs9 : S 9 = 0 := by simp [S, dimensionState, encoderRegs]
  have hs10 : S 10 = 0 := by simp [S, dimensionState, encoderRegs]
  have hs12 : S 12 = 0 := by simp [S, dimensionState, encoderRegs]
  have hs13 : S 13 = 0 := by simp [S, dimensionState, encoderRegs]
  have hs14 : S 14 = 0 := by simp [S, dimensionState, encoderRegs]
  have hs15 : S 15 = 0 := by simp [S, dimensionState, encoderRegs]
  have hs18 : S 18 = 0 := by simp [S, dimensionState, encoderRegs]
  have hs19 : S 19 = 0 := by simp [S, dimensionState, encoderRegs]
  have hsize : regSize S ≤ 10*(v+1) := dimensionState_encoderRegs_size false v
  have hsquare : v+1 ≤ (v+1)^2 := Nat.le_self_pow (by decide) _
  have hsize' : regSize S ≤ 100*(v+1)^2 := by omega
  have hp16 : v+1 ≤ (v+1)^16 := Nat.le_self_pow (by decide) _
  have hproduct : (v+1)^16 ≤ (C+1)*(v+1)^16 := by
    exact Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨n, hn, hnb⟩ := dimensionInit_exec false data (encoderRegs v)
  have hnb' : n ≤ 10000*(v+1) := by simpa [encoderRegs_size] using hnb
  have hbranch : ∃ m, OutputExec C data (.branch false 0 1 zeroMatrixInc complexPass)
      S [] (complexBodyRegs v) (complexBodyWord v data) m ∧
      m ≤ regCharge S + 10^35*(C+1)*(v+1)^16 := by
    by_cases hv : v = 0
    · have hguard : regCompare false 0 1 S = true := by simp [regCompare, hs0, hs1, hv]
      obtain ⟨m, hm, hmb⟩ := zeroMatrixInc_exec C data S 1 hs18 hs19 hs1 hs2 hs12 hs13
        hs14 hs15 (by simpa [hv] using hs6) []
      have hz : OutputExec C data zeroMatrixInc S [] (complexBodyRegs v) (complexBodyWord v data) m := by
        change OutputExec C data zeroMatrixInc S [] (Function.update S 10 (complexSlices v))
          (if v = 0 then matrixValueWord (minorValue 0 0) 1 else passWord none v data) m
        simp only [hv, complexSlices, if_true]
        simpa only [hs10, zero_add, List.append_nil] using hm
      have he : OutputExec C data (.branch false 0 1 zeroMatrixInc complexPass)
          S [] (complexBodyRegs v) (complexBodyWord v data) (regCharge S+m) := by
        apply OutputExec.branch (R := S) (T := complexBodyRegs v) (n := m)
        rw [hguard]
        exact hz
      refine ⟨_, he, ?_⟩
      have hm' := minorMatrixBound_mono C 1 (show regSize S ≤ 10 by simpa [hv] using hsize)
      have hm'' : minorMatrixBound C (regSize S) 1 ≤ 16900000000*(C+1)+2314 := by
        calc
          _ ≤ minorMatrixBound C 10 1 := hm'
          _ = _ := by simp [minorMatrixBound]; ring
      simp only [regCharge] at hmb
      simp only [hv, Nat.zero_add, one_pow, Nat.mul_one]
      omega
    · let cap := 100*(v+1)^2
      have hcap : S 10 + 4*v + scanCount (minorInc (2*v+1)) (2*v+1) ≤ cap := by
        have hcount := minorCount_le (2*v+1)
        dsimp [cap]
        rw [hs10, zero_add]
        nlinarith
      have hcount : 4*v + scanCount (minorInc (2*v+1)) (2*v+1) = complexSlices v := by
        have h := minorSliceCount v
        rw [complexSlices_pos v hv]
        omega
      have hguard : regCompare false 0 1 S = false := by simp [regCompare, hs0, hs1, hv]
      obtain ⟨m, hm, hmb⟩ := complexPass_exec C data S v (2*v+1) cap hs0 hlen rfl
        hs1 hs2 hs3 hs4 hs8 hs9 hs12 hs13 hs14 hs15 hs18 hs19 hs6 hs7 hcap []
      have hp : m ≤ complexPassBudget C (regSize S) v cap := by
        simpa only [complexPassBudget] using hmb
      have hb := complexPassBudget_le C (regSize S) v cap hsize' (by dsimp [cap]; exact le_rfl)
      have hz : OutputExec C data complexPass S [] (complexBodyRegs v) (complexBodyWord v data) m := by
        simpa [complexBodyRegs, complexBodyWord, hv, hs10, hcount, S] using hm
      have he : OutputExec C data (.branch false 0 1 zeroMatrixInc complexPass)
          S [] (complexBodyRegs v) (complexBodyWord v data) (regCharge S+m) := by
        apply OutputExec.branch (R := S) (T := complexBodyRegs v) (n := m)
        rw [hguard]
        exact hz
      exact ⟨_, he, by omega⟩
  obtain ⟨m, hm, hmb⟩ := hbranch
  refine ⟨n+1+m, ?_, ?_⟩
  · exact OutputExec.seq (OutputExec.reg [] hn) hm
  · simp only [regCharge] at hmb
    simp only [Nat.mul_assoc] at hmb ⊢
    omega

end TensorNP.BilinearEncoder

                                                       

namespace TensorNP.BilinearEncoder

theorem complex_payload_poly : CookPvsNP.PolyTimeComputable (graphEncoderValue complexPayload) := by
  apply graph_payload_poly_of_output complexPayload complexBody 16
  intro C
  refine ⟨10^45*(C+1), ?_⟩
  intro v G
  have hlen : (graphData G).length = v*v := by simpa [graphData] using (graphBits_valid G).1
  obtain ⟨n, he, hn⟩ := complexBody_exec C (graphData G) v hlen
  refine ⟨complexBodyRegs v, complexBodyWord v (graphData G), n, he, ?_, ?_, ?_⟩
  · simp only [Nat.mul_assoc] at hn ⊢
    omega
  · have hslices : complexSlices v ≤ 7*(v+1)^2 := by
      cases v with
      | zero => simp [complexSlices]
      | succ v => simp only [complexSlices]; nlinarith
    have hdim := dimensionState_encoderRegs_size false v
    have hu := regSize_update_le (dimensionState false (encoderRegs v)) 10 (complexSlices v)
    change regSize (complexBodyRegs v) ≤ _ at hu
    have hp : (v+1)^2 ≤ (v+1)^16 := pow_le_pow_right₀ (by omega) (by omega)
    have hl : v+1 ≤ (v+1)^2 := Nat.le_self_pow (by decide) _
    have hpos : 1 ≤ (v+1)^16 := Nat.pow_pos (by omega)
    have hprod : (v+1)^16 ≤ (C+1)*(v+1)^16 := Nat.le_mul_of_pos_left _ (by omega)
    simp only [Nat.mul_assoc]
    omega
  · cases v with
    | zero => simp [complexBodyRegs, complexBodyWord, dimensionState, encoderRegs,
        complexPayload, complexSlices]
    | succ v => simp [complexBodyRegs, complexBodyWord, dimensionState, encoderRegs,
        complexPayload, complexSlices]

end TensorNP.BilinearEncoder
end


/- Inlined module: LowHH -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def shiftHighPair (R : RegFile) : RegFile :=
  Function.update (Function.update R 1 (R 1 - R 7)) 2 (R 2 - R 7)

def swapCounts : RegCmd :=
  .seq (.assign 16 14) (.seq (.assign 14 15) (.seq (.assign 15 16) (.reset 16)))

def lowHH (coeff : RegCmd) : RegCmd :=
  .seq (.seq (.sub 1 7 (by decide)) (.sub 2 7 (by decide)))
    (.seq coeff (.seq swapCounts (.seq (.add 1 7 (by decide)) (.add 2 7 (by decide)))))

-- Routine register identities and the fixed swap are inactive finishing obligations.
theorem swapCounts_exec (data : List BSym) (R : RegFile) (h16 : R 16 = 0) :
    ∃ n, RegExec data swapCounts R (putCounts R (R 15) (R 14)) n ∧
      n ≤ 1000*(regSize R+1) := by
  let S := Function.update R 16 (R 14)
  let T := Function.update S 14 (S 15)
  let U := Function.update T 15 (T 16)
  have he1 : RegExec data (.assign 16 14) R S (regCharge R) := RegExec.assign R 16 14
  have he2 : RegExec data (.assign 14 15) S T (regCharge S) := RegExec.assign S 14 15
  have he3 : RegExec data (.assign 15 16) T U (regCharge T) := RegExec.assign T 15 16
  have he4 := RegExec.reset (data := data) U 16
  have hend : Function.update U 16 0 = putCounts R (R 15) (R 14) := by
    funext k
    fin_cases k <;> simp [S, T, U, putCounts, Function.update, h16]
  rw [hend] at he4
  have he := RegExec.seq he1 (RegExec.seq he2 (RegExec.seq he3 he4))
  have hs1 : regSize S ≤ regSize R + R 14 := regSize_update_le R 16 (R 14)
  have hs2 : regSize T ≤ regSize S + S 15 := regSize_update_le S 14 (S 15)
  have hs3 : regSize U ≤ regSize T + T 16 := regSize_update_le T 15 (T 16)
  have hs15 : S 15 = R 15 := by simp [S]
  have ht16 : T 16 = R 14 := by simp [S, T]
  have hr14 := reg_le_size R 14
  have hr15 := reg_le_size R 15
  refine ⟨_, he, ?_⟩
  simp only [regCharge]
  omega

theorem lowHH_restore (R : RegFile) (P M : ℕ) (h1 : R 7 ≤ R 1) (h2 : R 7 ≤ R 2) :
    let U := putCounts (shiftHighPair R) M P
    let V := Function.update U 1 (U 7 + U 1)
    Function.update V 2 (V 7 + V 2) = putCounts R M P := by
  dsimp only
  funext k
  fin_cases k <;> simp [putCounts, shiftHighPair] <;> omega

theorem lowHH_exec (data : List BSym) (coeff : RegCmd) (R : RegFile) (P M n : ℕ)
    (h1 : R 7 ≤ R 1) (h2 : R 7 ≤ R 2) (h16 : R 16 = 0)
    (hcoeff : RegExec data coeff (shiftHighPair R) (putCounts (shiftHighPair R) P M) n) :
    ∃ steps, RegExec data (lowHH coeff) R (putCounts R M P) steps ∧
      steps ≤ n + 10000*(regSize R+P+M+2) := by
  let A := Function.update R 1 (R 1 - R 7)
  let S := shiftHighPair R
  let T := putCounts S P M
  let U := putCounts S M P
  let V := Function.update U 1 (U 7 + U 1)
  have hs : RegExec data (.seq (.sub 1 7 (by decide)) (.sub 2 7 (by decide))) R S
      (regCharge R+1+regCharge A) := by
    simpa [A, S, shiftHighPair] using RegExec.seq
      (RegExec.sub (data := data) R 1 7 (by decide))
      (RegExec.sub (data := data) A 2 7 (by decide))
  have ht16 : T 16 = 0 := by simpa [T, putCounts, S, shiftHighPair] using h16
  obtain ⟨m, hm, hmb⟩ := swapCounts_exec data T ht16
  have htu : putCounts T (T 15) (T 14) = U := by
    funext k
    fin_cases k <;> simp [T, U, putCounts]
  rw [htu] at hm
  have ha := RegExec.seq (RegExec.add (data := data) U 1 7 (by decide))
    (RegExec.add (data := data) V 2 7 (by decide))
  rw [lowHH_restore R P M h1 h2] at ha
  have he := RegExec.seq hs (RegExec.seq hcoeff (RegExec.seq hm ha))
  refine ⟨_, he, ?_⟩
  have hsize : regSize A ≤ 2*regSize R ∧
      regSize T ≤ 3*regSize R+P+M ∧ regSize U ≤ 3*regSize R+P+M ∧
      regSize V ≤ 5*regSize R+P+M := by
    have hr1 := reg_le_size R 1
    have hr2 := reg_le_size R 2
    have hr7 := reg_le_size R 7
    have ha := regSize_update_le R 1 (R 1 - R 7)
    change regSize A ≤ _ at ha
    have hs := regSize_update_le A 2 (R 2 - R 7)
    change regSize S ≤ _ at hs
    have ht1 := regSize_update_le S 14 P
    have ht2 := regSize_update_le (Function.update S 14 P) 15 M
    change regSize T ≤ _ at ht2
    have hu1 := regSize_update_le S 14 M
    have hu2 := regSize_update_le (Function.update S 14 M) 15 P
    change regSize U ≤ _ at hu2
    have hv := regSize_update_le U 1 (U 7 + U 1)
    change regSize V ≤ _ at hv
    have hu7 : U 7 = R 7 := by simp [U, S, shiftHighPair, putCounts]
    have hu1val : U 1 = R 1 - R 7 := by simp [U, S, shiftHighPair, putCounts]
    have hd1 := Nat.sub_le (R 1) (R 7)
    have hd2 := Nat.sub_le (R 2) (R 7)
    omega
  rcases hsize with ⟨hA, hT, hU, hV⟩
  simp only [regCharge] at *
  omega

end TensorNP.BilinearEncoder
end


/- Inlined module: HighShift -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def shiftRow (R : RegFile) : RegFile := Function.update R 1 (R 1 - R 7)
def shiftCol (R : RegFile) : RegFile := Function.update R 2 (R 2 - R 7)

def highHL (coeff : RegCmd) : RegCmd :=
  .seq (.sub 1 7 (by decide)) (.seq coeff (.add 1 7 (by decide)))

def highLH (coeff : RegCmd) : RegCmd :=
  .seq (.sub 2 7 (by decide)) (.seq coeff (.add 2 7 (by decide)))

private theorem restoreShift (R : RegFile) (r : Fin 21) (P M : ℕ)
    (hr : r = 1 ∨ r = 2) (hle : R 7 ≤ R r) :
    let T := putCounts (Function.update R r (R r - R 7)) P M
    Function.update T r (T 7 + T r) = putCounts R P M := by
  rcases hr with rfl | rfl <;> dsimp only <;> funext k <;> fin_cases k <;>
    simp [putCounts] <;> omega

private theorem highShift_exec (data : List BSym) (coeff : RegCmd) (R : RegFile)
    (r : Fin 21) (hr : r = 1 ∨ r = 2) (hne : r ≠ 7) (P M n : ℕ)
    (hle : R 7 ≤ R r)
    (hcoeff : RegExec data coeff (Function.update R r (R r - R 7))
      (putCounts (Function.update R r (R r - R 7)) P M) n) :
    ∃ steps, RegExec data (.seq (.sub r 7 hne) (.seq coeff (.add r 7 hne))) R (putCounts R P M) steps ∧
      steps ≤ n + 1000*(regSize R+P+M+2) := by
  let S := Function.update R r (R r - R 7)
  let T := putCounts S P M
  have he1 : RegExec data (.sub r 7 hne) R S (regCharge R) := RegExec.sub R r 7 hne
  have he3 := RegExec.add (data := data) T r 7 hne
  have hend : Function.update T r (T 7 + T r) = putCounts R P M := restoreShift R r P M hr hle
  rw [hend] at he3
  have he := RegExec.seq he1 (RegExec.seq hcoeff he3)
  refine ⟨_, he, ?_⟩
  have hrsize := reg_le_size R r
  have hs := regSize_update_le R r (R r - R 7)
  change regSize S ≤ _ at hs
  have ht1 := regSize_update_le S 14 P
  have ht2 := regSize_update_le (Function.update S 14 P) 15 M
  change regSize T ≤ _ at ht2
  have hd := Nat.sub_le (R r) (R 7)
  simp only [regCharge]
  omega

theorem highHL_exec (data : List BSym) (coeff : RegCmd) (R : RegFile) (P M n : ℕ)
    (h1 : R 7 ≤ R 1) (hcoeff : RegExec data coeff (shiftRow R) (putCounts (shiftRow R) P M) n) :
    ∃ steps, RegExec data (highHL coeff) R (putCounts R P M) steps ∧
      steps ≤ n + 1000*(regSize R+P+M+2) := by
  exact highShift_exec data coeff R 1 (Or.inl rfl) (by decide) P M n h1 hcoeff

theorem highLH_exec (data : List BSym) (coeff : RegCmd) (R : RegFile) (P M n : ℕ)
    (h2 : R 7 ≤ R 2) (hcoeff : RegExec data coeff (shiftCol R) (putCounts (shiftCol R) P M) n) :
    ∃ steps, RegExec data (highLH coeff) R (putCounts R P M) steps ∧
      steps ≤ n + 1000*(regSize R+P+M+2) := by
  exact highShift_exec data coeff R 2 (Or.inr rfl) (by decide) P M n h2 hcoeff

end TensorNP.BilinearEncoder
end


/- Inlined module: RealCoefficient -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def realArg (R : RegFile) : RegFile :=
  if R 1 < R 7 then if R 2 < R 7 then R else shiftCol R
  else if R 2 < R 7 then shiftRow R else shiftHighPair R

def realCounts (high : Bool) (P M : RegFile → ℕ) (R : RegFile) : ℕ × ℕ :=
  if R 1 < R 7 then
    if R 2 < R 7 then (if high then (0, 0) else (P R, M R))
    else (if high then (P (shiftCol R), M (shiftCol R)) else (0, 0))
  else
    if R 2 < R 7 then (if high then (P (shiftRow R), M (shiftRow R)) else (0, 0))
    else (if high then (0, 0) else (M (shiftHighPair R), P (shiftHighPair R)))

def realCoefficient (high : Bool) (coeff : RegCmd) : RegCmd :=
  .branch true 1 7
    (.branch true 2 7 (if high then .skip else coeff) (if high then highLH coeff else .skip))
    (.branch true 2 7 (if high then highHL coeff else .skip) (if high then .skip else lowHH coeff))

theorem realCoefficient_exec (data : List BSym) (high : Bool) (coeff : RegCmd)
    (P M : RegFile → ℕ) (R : RegFile) (B K : ℕ)
    (h14 : R 14 = 0) (h15 : R 15 = 0) (h16 : R 16 = 0)
    (hbase : ∃ n, RegExec data coeff (realArg R)
      (putCounts (realArg R) (P (realArg R)) (M (realArg R))) n ∧ n ≤ B)
    (hcounts : P (realArg R) + M (realArg R) ≤ K) :
    ∃ steps, RegExec data (realCoefficient high coeff) R
      (putCounts R (realCounts high P M R).1 (realCounts high P M R).2) steps ∧
      steps ≤ B + 20000*(regSize R+K+2) := by
  cases high with
  | true =>
    by_cases hr : R 1 < R 7 <;> by_cases hc : R 2 < R 7
    · have hz : putCounts R 0 0 = R := by
        funext k
        fin_cases k <;> simp [putCounts, h14, h15]
      have he := RegExec.branch (data := data) (R := R) (less := true) (r := 1) (s := 7)
        (yes := .branch true 2 7 .skip (highLH coeff)) (no := .branch true 2 7 (highHL coeff) .skip)
        (by simpa [regCompare, hr] using
          (RegExec.branch (data := data) (R := R) (less := true) (r := 2) (s := 7)
            (yes := .skip) (no := highLH coeff) (by simpa [regCompare, hc] using RegExec.skip R)))
      refine ⟨regCharge R + (regCharge R+1), ?_, ?_⟩
      · simpa [realCoefficient, realCounts, hr, hc, hz] using he
      · simp only [regCharge]
        omega
    · have harg : realArg R = shiftCol R := by simp [realArg, hr, hc]
      rw [harg] at hbase hcounts
      obtain ⟨n, hn, hnb⟩ := hbase
      obtain ⟨m, hm, hmb⟩ := highLH_exec data coeff R (P (shiftCol R)) (M (shiftCol R)) n
        (Nat.le_of_not_gt hc) hn
      have he := RegExec.branch (data := data) (R := R) (less := true) (r := 1) (s := 7)
        (yes := .branch true 2 7 .skip (highLH coeff)) (no := .branch true 2 7 (highHL coeff) .skip)
        (by simpa [regCompare, hr] using
          (RegExec.branch (data := data) (R := R) (less := true) (r := 2) (s := 7)
            (yes := .skip) (no := highLH coeff) (by simpa [regCompare, hc] using hm)))
      refine ⟨regCharge R + (regCharge R+m), ?_, ?_⟩
      · simpa [realCoefficient, realCounts, hr, hc] using he
      · simp only [regCharge]
        omega
    · have harg : realArg R = shiftRow R := by simp [realArg, hr, hc]
      rw [harg] at hbase hcounts
      obtain ⟨n, hn, hnb⟩ := hbase
      obtain ⟨m, hm, hmb⟩ := highHL_exec data coeff R (P (shiftRow R)) (M (shiftRow R)) n
        (Nat.le_of_not_gt hr) hn
      have he := RegExec.branch (data := data) (R := R) (less := true) (r := 1) (s := 7)
        (yes := .branch true 2 7 .skip (highLH coeff)) (no := .branch true 2 7 (highHL coeff) .skip)
        (by simpa [regCompare, hr] using
          (RegExec.branch (data := data) (R := R) (less := true) (r := 2) (s := 7)
            (yes := highHL coeff) (no := .skip) (by simpa [regCompare, hc] using hm)))
      refine ⟨regCharge R + (regCharge R+m), ?_, ?_⟩
      · simpa [realCoefficient, realCounts, hr, hc] using he
      · simp only [regCharge]
        omega
    · have hz : putCounts R 0 0 = R := by
        funext k
        fin_cases k <;> simp [putCounts, h14, h15]
      have he := RegExec.branch (data := data) (R := R) (less := true) (r := 1) (s := 7)
        (yes := .branch true 2 7 .skip (highLH coeff)) (no := .branch true 2 7 (highHL coeff) .skip)
        (by simpa [regCompare, hr] using
          (RegExec.branch (data := data) (R := R) (less := true) (r := 2) (s := 7)
            (yes := highHL coeff) (no := .skip) (by simpa [regCompare, hc] using RegExec.skip R)))
      refine ⟨regCharge R + (regCharge R+1), ?_, ?_⟩
      · simpa [realCoefficient, realCounts, hr, hc, hz] using he
      · simp only [regCharge]
        omega
  | false =>
    by_cases hr : R 1 < R 7
    · by_cases hc : R 2 < R 7
      · have harg : realArg R = R := by simp [realArg, hr, hc]
        rw [harg] at hbase hcounts
        obtain ⟨n, hn, hnb⟩ := hbase
        have he := RegExec.branch (data := data) (R := R) (less := true) (r := 1) (s := 7)
          (yes := .branch true 2 7 coeff .skip) (no := .branch true 2 7 .skip (lowHH coeff))
          (by simpa [regCompare, hr] using
            (RegExec.branch (data := data) (R := R) (less := true) (r := 2) (s := 7)
              (yes := coeff) (no := .skip) (by simpa [regCompare, hc] using hn)))
        refine ⟨regCharge R + (regCharge R+n), ?_, ?_⟩
        · simpa [realCoefficient, realCounts, hr, hc] using he
        · simp only [regCharge]
          omega
      · have hz : putCounts R 0 0 = R := by
          funext k
          fin_cases k <;> simp [putCounts, h14, h15]
        have he := RegExec.branch (data := data) (R := R) (less := true) (r := 1) (s := 7)
          (yes := .branch true 2 7 coeff .skip) (no := .branch true 2 7 .skip (lowHH coeff))
          (by simpa [regCompare, hr] using
            (RegExec.branch (data := data) (R := R) (less := true) (r := 2) (s := 7)
              (yes := coeff) (no := .skip) (by simpa [regCompare, hc] using RegExec.skip R)))
        refine ⟨regCharge R + (regCharge R+1), ?_, ?_⟩
        · simpa [realCoefficient, realCounts, hr, hc, hz] using he
        · simp only [regCharge]
          omega
    · by_cases hc : R 2 < R 7
      · have hz : putCounts R 0 0 = R := by
          funext k
          fin_cases k <;> simp [putCounts, h14, h15]
        have he := RegExec.branch (data := data) (R := R) (less := true) (r := 1) (s := 7)
          (yes := .branch true 2 7 coeff .skip) (no := .branch true 2 7 .skip (lowHH coeff))
          (by simpa [regCompare, hr] using
            (RegExec.branch (data := data) (R := R) (less := true) (r := 2) (s := 7)
              (yes := .skip) (no := lowHH coeff) (by simpa [regCompare, hc] using RegExec.skip R)))
        refine ⟨regCharge R + (regCharge R+1), ?_, ?_⟩
        · simpa [realCoefficient, realCounts, hr, hc, hz] using he
        · simp only [regCharge]
          omega
      · have harg : realArg R = shiftHighPair R := by simp [realArg, hr, hc]
        rw [harg] at hbase hcounts
        obtain ⟨n, hn, hnb⟩ := hbase
        obtain ⟨m, hm, hmb⟩ := lowHH_exec data coeff R
          (P (shiftHighPair R)) (M (shiftHighPair R)) n
          (Nat.le_of_not_gt hr) (Nat.le_of_not_gt hc) h16 hn
        have he := RegExec.branch (data := data) (R := R) (less := true) (r := 1) (s := 7)
          (yes := .branch true 2 7 coeff .skip) (no := .branch true 2 7 .skip (lowHH coeff))
          (by simpa [regCompare, hr] using
            (RegExec.branch (data := data) (R := R) (less := true) (r := 2) (s := 7)
              (yes := .skip) (no := lowHH coeff) (by simpa [regCompare, hc] using hm)))
        refine ⟨regCharge R + (regCharge R+m), ?_, ?_⟩
        · simpa [realCoefficient, realCounts, hr, hc] using he
        · simp only [regCharge]
          omega

end TensorNP.BilinearEncoder
end


/- Inlined module: RealValues -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def coordState (R : RegFile) (row col : ℕ) : RegFile :=
  Function.update (Function.update R 1 row) 2 col

theorem realCounts_value (high : Bool) (P M : RegFile → ℕ) (R : RegFile)
    (A : ℕ → ℕ → ℚ)
    (h : ∀ row col, (P (coordState R row col) : ℚ) - (M (coordState R row col) : ℚ) = A row col) :
    ((realCounts high P M R).1 : ℚ) - ((realCounts high P M R).2 : ℚ) =
      realEntryValue high (R 7) A (R 1) (R 2) := by
  have hbase : coordState R (R 1) (R 2) = R := by
    simp [coordState]
  have hcol : coordState R (R 1) (R 2 - R 7) = shiftCol R := by
    simp [coordState, shiftCol]
  have hrow : coordState R (R 1 - R 7) (R 2) = shiftRow R := by
    simp [coordState, shiftRow]
  have hpair : coordState R (R 1 - R 7) (R 2 - R 7) = shiftHighPair R := rfl
  obtain ⟨h0, h1, h2, h3⟩ := And.intro (h (R 1) (R 2))
    (And.intro (h (R 1) (R 2 - R 7))
      (And.intro (h (R 1 - R 7) (R 2)) (h (R 1 - R 7) (R 2 - R 7))))
  simp only [hbase, hcol, hrow, hpair] at h0 h1 h2 h3
  cases high <;> by_cases hr : R 1 < R 7 <;> by_cases hc : R 2 < R 7 <;>
    simp [realCounts, realEntryValue, hr, hc, h0, h1, h2]; linarith

theorem realCounts_le (high : Bool) (P M : RegFile → ℕ) (R : RegFile) (K : ℕ)
    (h : P (realArg R) + M (realArg R) ≤ K) :
    (realCounts high P M R).1 + (realCounts high P M R).2 ≤ K := by
  cases high <;> by_cases hr : R 1 < R 7 <;> by_cases hc : R 2 < R 7 <;>
    simp [realCounts, realArg, hr, hc] at * <;> omega

theorem realArg_other (R : RegFile) (r : Fin 21) (h1 : r ≠ 1) (h2 : r ≠ 2) :
    realArg R r = R r := by
  unfold realArg
  split_ifs <;> simp [shiftRow, shiftCol, shiftHighPair, h1, h2]

theorem realArg_size_le (R : RegFile) : regSize (realArg R) ≤ 3 * regSize R := by
  obtain ⟨h1, h2⟩ := And.intro (reg_le_size R 1) (reg_le_size R 2)
  obtain ⟨hu1, hu2, hu12⟩ := And.intro (regSize_update_le R 1 (R 1 - R 7))
    (And.intro (regSize_update_le R 2 (R 2 - R 7))
      (regSize_update_le (Function.update R 1 (R 1 - R 7)) 2 (R 2 - R 7)))
  unfold realArg
  split_ifs <;> (try dsimp [shiftRow, shiftCol, shiftHighPair]) <;> omega

end TensorNP.BilinearEncoder
end


/- Inlined module: RealMatrices -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def colorPositive (data : List BSym) (f : Fin 4) (R : RegFile) : ℕ :=
  rawPositiveCount (R 0) data f.val (R 3) (R 1) (R 2)
def colorNegative (f : Fin 4) (R : RegFile) : ℕ :=
  rawNegativeCount (R 0) f.val (R 3) (R 1) (R 2)
def realMinorEntryWord (high : Bool) (N a b row col : ℕ) : List BSym :=
  TensorNP.Eigen.encRat (realEntryValue high N (minorValue a b) row col)
def realColorEntryWord (high : Bool) (N v : ℕ) (data : List BSym)
    (f vertex row col : ℕ) : List BSym :=
  TensorNP.Eigen.encRat (realEntryValue high N (colorValue v data f vertex) row col)

theorem realEntry_spec (C : ℕ) (data : List BSym) (R : RegFile) (N : ℕ)
    (high : Bool) (coeff : RegCmd) (P M : RegFile → ℕ) (A : ℕ → ℕ → ℚ)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0)
    (h16 : R 16 = 0) (h7 : R 7 = N)
    (hbase : ∀ row col, row < N+N → col < N+N →
      let T := entryCoords (cellState R row col)
      ∃ n, RegExec data coeff (realArg T) (putCounts (realArg T) (P (realArg T)) (M (realArg T))) n ∧
        n ≤ 1000000*(3*regSize T+2)^4)
    (hcounts : ∀ row col, P (realArg (entryCoords (cellState R row col))) +
      M (realArg (entryCoords (cellState R row col))) ≤ 3*R 0+2)
    (hvalue : ∀ row col a b,
      let T := entryCoords (cellState R row col)
      (P (coordState T a b) : ℚ) - (M (coordState T a b) : ℚ) = A a b) :
    MatrixEntrySpec C data (matrixEntry (realCoefficient high coeff))
      (fun row col => TensorNP.Eigen.encRat (realEntryValue high N A row col)) R (N+N)
      (100000000000000000000*(C+1)*(regSize R+N+2)^4) := by
  intro row col tail hr hc
  let S := cellState R row col
  let T := entryCoords S
  have hS : S 1 = 0 ∧ S 2 = 0 ∧ S 14 = 0 ∧ S 15 = 0 ∧ S 0 = R 0 := by
    simp [S, cellState, h1, h2, h14, h15]
  have hT : T 14 = 0 ∧ T 15 = 0 ∧ T 16 = 0 ∧ T 7 = N ∧ T 1 = row ∧ T 2 = col := by
    simp [T, entryCoords, S, cellState, h14, h15, h16, h7]
  have hcoeff := realCoefficient_exec data high coeff P M T (1000000*(3*regSize T+2)^4)
    (3*R 0+2) hT.1 hT.2.1 hT.2.2.1 (hbase row col hr hc) (hcounts row col)
  have hcc : (realCounts high P M T).1 + (realCounts high P M T).2 ≤ 3*S 0+2 := by
    simpa only [hS.2.2.2.2] using realCounts_le high P M T (3*R 0+2) (hcounts row col)
  obtain ⟨steps, he, hb⟩ := matrixEntry_exec C data (realCoefficient high coeff) S
    (realCounts high P M T).1 (realCounts high P M T).2
    (1000000*(3*regSize T+2)^4 + 20000*(regSize T+(3*R 0+2)+2))
    hS.1 hS.2.1 hS.2.2.1 hS.2.2.2.1 hcc hcoeff tail
  have hv : ((realCounts high P M T).1 : ℚ) - ((realCounts high P M T).2 : ℚ) =
      realEntryValue high N A row col := by
    simpa only [hT.2.2.2.1, hT.2.2.2.2.1, hT.2.2.2.2.2] using
      realCounts_value high P M T A (hvalue row col)
  refine ⟨steps, ?_, ?_⟩
  · simpa only [hv, S] using he
  · have hs : regSize S ≤ regSize R+row+col := by
      dsimp [S, cellState]
      have h := regSize_update_le (Function.update R 12 row) 13 col
      have h' := regSize_update_le R 12 row
      omega
    have ht : regSize T ≤ regSize S+row+col := by
      dsimp [T, entryCoords]
      have h := regSize_update_le (Function.update S 1 (S 12)) 2 (S 13)
      have h' := regSize_update_le S 1 (S 12)
      have h12 : S 12 = row := by simp [S, cellState]
      have h13 : S 13 = col := by simp [S, cellState]
      omega
    let X := regSize R + N + 2
    have hx : 1 ≤ X ∧ regSize S + 2 ≤ 4*X ∧ 3*regSize T + 2 ≤ 24*X ∧
        regSize T + (3*R 0+2) + 2 ≤ 16*X := by
      have h0 := reg_le_size R 0
      dsimp [X]
      omega
    have hp4 : (3*regSize T+2)^4 ≤ 331776*X^4 := by
      calc
        _ ≤ (24*X)^4 := Nat.pow_le_pow_left hx.2.2.1 4
        _ = _ := by ring
    have hp2 : (regSize S+2)^2 ≤ 16*X^4 := by
      calc
        _ ≤ (4*X)^2 := Nat.pow_le_pow_left hx.2.1 2
        _ = 16*X^2 := by ring
        _ ≤ 16*X^4 := Nat.mul_le_mul_left 16 (pow_le_pow_right₀ hx.1 (by omega))
    have hlin : regSize T + (3*R 0+2) + 2 ≤ 16*X^4 := by
      calc
        _ ≤ 16*X := hx.2.2.2
        _ ≤ 16*X^4 := Nat.mul_le_mul_left 16 (Nat.le_self_pow (by decide) _)
    obtain ⟨hb4, hb2, hbl⟩ := And.intro (Nat.mul_le_mul_left 1000000 hp4)
      (And.intro (Nat.mul_le_mul_left (16*C+1000000) hp2) (Nat.mul_le_mul_left 20000 hlin))
    have hsum : 1000000*(331776*X^4) + 20000*(16*X^4) +
        (16*C+1000000)*(16*X^4) ≤ 100000000000000000000*(C+1)*X^4 := by
      calc
        _ = (331792320000+256*C)*X^4 := by ring
        _ ≤ (100000000000000000000*(C+1))*X^4 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
    change steps ≤ 100000000000000000000*(C+1)*X^4
    omega

theorem realMinorEntry_spec (C : ℕ) (data : List BSym) (R : RegFile) (N : ℕ) (high : Bool)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0)
    (h16 : R 16 = 0) (h7 : R 7 = N) :
    MatrixEntrySpec C data (matrixEntry (realCoefficient high minorProgram))
      (realMinorEntryWord high N (R 18) (R 19)) R (N+N)
      (100000000000000000000*(C+1)*(regSize R+N+2)^4) := by
  apply realEntry_spec C data R N high minorProgram minorPositive minorNegative
    (minorValue (R 18) (R 19)) h1 h2 h14 h15 h16 h7
  case hbase =>
    intro row col hr hc
    let T := entryCoords (cellState R row col)
    have hU : realArg T 14 = 0 ∧ realArg T 15 = 0 := by
      simp [realArg_other, T, entryCoords, cellState, h14, h15]
    obtain ⟨n, hn, hb⟩ := minorProgram_exec data (realArg T) hU.1 hU.2
    refine ⟨n, hn, ?_⟩
    have hs := realArg_size_le T
    have hp := Nat.le_self_pow (by decide : 4 ≠ 0) (3*regSize T+2)
    change n ≤ 1000000*(3*regSize T+2)^4
    omega
  case hcounts =>
    intro row col
    have hp := minorPositive_le (realArg (entryCoords (cellState R row col)))
    have hn := minorNegative_le (realArg (entryCoords (cellState R row col)))
    omega
  case hvalue =>
    intro row col a b
    simp [minorPositive, minorNegative, minorValue, coordState, entryCoords, cellState]

theorem realColorEntry_spec (C : ℕ) (data : List BSym) (R : RegFile) (N : ℕ) (high : Bool) (f : Fin 4)
    (hlen : data.length = R 0 * R 0) (hvertex : R 3 < R 0)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h4 : R 4 = 0) (h8 : R 8 = 0) (h9 : R 9 = 0)
    (h14 : R 14 = 0) (h15 : R 15 = 0) (h16 : R 16 = 0) (h7 : R 7 = N) :
    MatrixEntrySpec C data (matrixEntry (realCoefficient high (colorFamily f)))
      (realColorEntryWord high N (R 0) data f.val (R 3)) R (N+N)
      (100000000000000000000*(C+1)*(regSize R+N+2)^4) := by
  apply realEntry_spec C data R N high (colorFamily f) (colorPositive data f) (colorNegative f)
    (colorValue (R 0) data f.val (R 3)) h1 h2 h14 h15 h16 h7
  case hbase =>
    intro row col hr hc
    let T := entryCoords (cellState R row col)
    let U := realArg T
    have hU : U 0 = R 0 ∧ U 3 = R 3 ∧ U 4 = 0 ∧ U 8 = 0 ∧ U 9 = 0 ∧ U 14 = 0 ∧ U 15 = 0 := by
      simp [U, realArg_other, T, entryCoords, cellState, h4, h8, h9, h14, h15]
    obtain ⟨n, hn, hb⟩ := colorFamily_exec data U f
      (by simpa only [hU.1, hU.2.1] using hvertex) (by simpa only [hU.1] using hlen)
      hU.2.2.1 hU.2.2.2.2.1 hU.2.2.2.1 hU.2.2.2.2.2.1 hU.2.2.2.2.2.2
    refine ⟨n, hn, ?_⟩
    change n ≤ 1000000*(3*regSize T+2)^4
    apply hb.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    have hs := realArg_size_le T
    change regSize U ≤ _ at hs
    omega
  case hcounts =>
    intro row col
    let U := realArg (entryCoords (cellState R row col))
    have hu : U 0 = R 0 := by simp [U, realArg_other, entryCoords, cellState]
    change colorPositive data f U + colorNegative f U ≤ 3*R 0+2
    simpa only [colorPositive, colorNegative, hu] using rawCounts_le (U 0) data f.val (U 3) (U 1) (U 2)
  case hvalue =>
    intro row col a b
    simp [colorPositive, colorNegative, colorValue, coordState, entryCoords, cellState]

def realMatrixBound (C size N : ℕ) : ℕ :=
  100*(size+1)+1+((N+N)*(100*(size+(N+N)+1)+
    (N+N)*(100000000000000000000*(C+1)*(size+N+2)^4+5)+7)+1)

theorem realMatrix_exec_of_spec (C : ℕ) (data : List BSym) (R : RegFile) (N : ℕ)
    (entry : OutputCmd) (E : ℕ → ℕ → List BSym)
    (hspec : MatrixEntrySpec C data entry E R (N+N)
      (100000000000000000000*(C+1)*(regSize R+N+2)^4))
    (h6 : R 6 = N+N) (h12 : R 12 = 0) (h13 : R 13 = 0) (tail : List BSym) :
    ∃ steps, OutputExec C data (matrixProgram entry) R tail R
      (matrixChunk E (N+N) (N+N) ++ tail) steps ∧ steps ≤ realMatrixBound C (regSize R) N := by
  have hQ : ∀ row, row < N+N → regCharge (cellState R row 0) ≤
      100*(regSize R+(N+N)+1) := by
    intro row hr
    have hs : regSize (cellState R row 0) ≤ regSize R+row := by
      have h := regSize_update_le (Function.update R 12 row) 13 0
      have h' := regSize_update_le R 12 row
      dsimp [cellState]
      omega
    simp only [regCharge]
    omega
  simpa only [realMatrixBound, regCharge] using
    matrixProgram_exec C data entry E R (N+N) _ _ h6 h12 h13 hspec hQ tail

theorem realMinorMatrix_exec (C : ℕ) (data : List BSym) (R : RegFile) (N : ℕ) (high : Bool)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0)
    (h16 : R 16 = 0) (h7 : R 7 = N) (h6 : R 6 = N+N)
    (h12 : R 12 = 0) (h13 : R 13 = 0) (tail : List BSym) :
    ∃ steps, OutputExec C data (matrixProgram (matrixEntry (realCoefficient high minorProgram))) R tail R
      (matrixChunk (realMinorEntryWord high N (R 18) (R 19)) (N+N) (N+N) ++ tail) steps ∧
      steps ≤ realMatrixBound C (regSize R) N := by
  exact realMatrix_exec_of_spec C data R N _ _
    (realMinorEntry_spec C data R N high h1 h2 h14 h15 h16 h7) h6 h12 h13 tail

theorem realColorMatrix_exec (C : ℕ) (data : List BSym) (R : RegFile) (N : ℕ) (high : Bool) (f : Fin 4)
    (hlen : data.length = R 0 * R 0) (hvertex : R 3 < R 0)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h4 : R 4 = 0) (h8 : R 8 = 0) (h9 : R 9 = 0)
    (h14 : R 14 = 0) (h15 : R 15 = 0) (h16 : R 16 = 0) (h7 : R 7 = N)
    (h6 : R 6 = N+N) (h12 : R 12 = 0) (h13 : R 13 = 0) (tail : List BSym) :
    ∃ steps, OutputExec C data (matrixProgram (matrixEntry (realCoefficient high (colorFamily f)))) R tail R
      (matrixChunk (realColorEntryWord high N (R 0) data f.val (R 3)) (N+N) (N+N) ++ tail) steps ∧
      steps ≤ realMatrixBound C (regSize R) N := by
  exact realMatrix_exec_of_spec C data R N _ _
    (realColorEntry_spec C data R N high f hlen hvertex h1 h2 h4 h8 h9 h14 h15 h16 h7)
    h6 h12 h13 tail

end TensorNP.BilinearEncoder
end


/- Inlined module: GenericColor -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def genericColorOne (emit : Fin 4 → OutputCmd) (f : Fin 4) : OutputCmd :=
  .seq (.reg (.assign 3 0)) (.down 3 (.seq (emit f) (.reg (.inc 10))))

def genericColorPass (emit : Fin 4 → OutputCmd) : OutputCmd :=
  .seq (genericColorOne emit 3) (.seq (genericColorOne emit 2)
    (.seq (genericColorOne emit 1) (genericColorOne emit 0)))

private theorem genericColor_scanCount_one (n : ℕ) : scanCount (fun _ => 1) n = n := by
  simp [scanCount]

private theorem genericColorOne_exec (C : ℕ) (data : List BSym) (R : RegFile)
    (emit : Fin 4 → OutputCmd) (W : Fin 4 → ℕ → List BSym) (f : Fin 4) (v cap B Q L : ℕ)
    (h0 : R 0 = v)
    (hem : ∀ f i L tail, i < v → L ≤ cap → ∃ n,
      OutputExec C data (emit f) (vertexScanState R i L) tail
        (vertexScanState R i L) (W f i ++ tail) n ∧ n ≤ B)
    (hcharge : ∀ i L, i ≤ v → L ≤ cap → regCharge (vertexScanState R i L) ≤ Q)
    (hcap : L+v ≤ cap) (tail : List BSym) :
    ∃ steps, OutputExec C data (genericColorOne emit f) (vertexScanState R 0 L) tail
      (vertexScanState R 0 (L+v)) (scanChunk (W f) v ++ tail) steps ∧
      steps ≤ Q+1+v*(B+Q+6)+1 := by
  have hbody : ∀ i L' tail', i < v → L'+1 ≤ cap → ∃ n,
      OutputExec C data (.seq (emit f) (.reg (.inc 10))) (vertexScanState R i L') tail'
        (vertexScanState R i (L'+1)) (W f i ++ tail') n ∧ n ≤ B+Q+1 := by
    intro i L' tail' hi hL
    obtain ⟨n, he, hn⟩ := hem f i L' tail' hi (by omega)
    have hq := hcharge i L' (by omega) (by omega)
    have hinc := OutputExec.reg (C := C) (W f i ++ tail')
      (RegExec.inc (data := data) (vertexScanState R i L') 10)
    have hex := OutputExec.seq he hinc
    refine ⟨n+1+regCharge (vertexScanState R i L'), ?_, ?_⟩
    · simpa only [vertexScanState_inc10] using hex
    · omega
  have hcap' : L+scanCount (fun _ => 1) v ≤ cap := by simpa only [genericColor_scanCount_one] using hcap
  obtain ⟨n, he, hn⟩ := sliceScan_exec C data (.seq (emit f) (.reg (.inc 10))) 3
    (fun i L' => vertexScanState R i L') (W f) (fun _ => 1) v (B+Q+1) cap
    (fun i L' => vertexScanState_at3 R i L')
    (fun i L' => vertexScanState_down3 R i L') hbody v le_rfl L hcap' tail
  have hstart : Function.update (vertexScanState R 0 L) 3 ((vertexScanState R 0 L) 0) =
      vertexScanState R v L := by
    funext k
    by_cases hk3 : k = 3 <;> by_cases hk10 : k = 10 <;>
      simp [vertexScanState, Function.update, hk3, hk10, h0]
  have hassign := OutputExec.reg (C := C) tail
    (RegExec.assign (data := data) (vertexScanState R 0 L) 3 0)
  rw [hstart] at hassign
  have he' : OutputExec C data (.down 3 (.seq (emit f) (.reg (.inc 10)))) (vertexScanState R v L) tail
      (vertexScanState R 0 (L+v)) (scanChunk (W f) v ++ tail) n := by
    simpa only [genericColor_scanCount_one] using he
  have hex := OutputExec.seq hassign he'
  have hq := hcharge 0 L (by omega) (by omega)
  have hbterm : B+Q+1+5 = B+Q+6 := by omega
  rw [hbterm] at hn
  refine ⟨regCharge (vertexScanState R 0 L)+1+n, hex, ?_⟩
  omega

theorem genericColorPass_exec (C : ℕ) (data : List BSym) (R : RegFile)
    (emit : Fin 4 → OutputCmd) (W : Fin 4 → ℕ → List BSym) (v cap B Q : ℕ)
    (h0 : R 0 = v) (h3 : R 3 = 0)
    (hem : ∀ f i L tail, i < v → L ≤ cap → ∃ n,
      OutputExec C data (emit f) (vertexScanState R i L) tail
        (vertexScanState R i L) (W f i ++ tail) n ∧ n ≤ B)
    (hcharge : ∀ i L, i ≤ v → L ≤ cap → regCharge (vertexScanState R i L) ≤ Q)
    (hcap : R 10+4*v ≤ cap) (tail : List BSym) :
    ∃ steps, OutputExec C data (genericColorPass emit) R tail
      (Function.update R 10 (R 10+4*v))
      ((scanChunk (W 0) v ++ scanChunk (W 1) v ++ scanChunk (W 2) v ++ scanChunk (W 3) v) ++ tail) steps ∧
      steps ≤ 4*(Q+1+v*(B+Q+6)+1)+3 := by
  let W3 := scanChunk (W 3) v
  let W2 := scanChunk (W 2) v
  let W1 := scanChunk (W 1) v
  let W0 := scanChunk (W 0) v
  obtain ⟨n3, he3, hb3⟩ := genericColorOne_exec C data R emit W 3 v cap B Q (R 10) h0 hem hcharge (by omega) tail
  obtain ⟨n2, he2, hb2⟩ := genericColorOne_exec C data R emit W 2 v cap B Q (R 10+v) h0 hem hcharge (by omega) (W3 ++ tail)
  obtain ⟨n1, he1, hb1⟩ := genericColorOne_exec C data R emit W 1 v cap B Q (R 10+v+v) h0 hem hcharge (by omega) (W2 ++ (W3 ++ tail))
  obtain ⟨n0, he0, hb0⟩ := genericColorOne_exec C data R emit W 0 v cap B Q (R 10+v+v+v) h0 hem hcharge (by omega) (W1 ++ (W2 ++ (W3 ++ tail)))
  have hstart : vertexScanState R 0 (R 10) = R := by
    funext k
    by_cases hk3 : k = 3 <;> by_cases hk10 : k = 10 <;>
      simp [vertexScanState, Function.update, hk3, hk10, h3]
  rw [hstart] at he3
  have hfinal : R 10+v+v+v+v = R 10+4*v := by omega
  rw [hfinal] at he0
  have hend : vertexScanState R 0 (R 10+4*v) = Function.update R 10 (R 10+4*v) := by
    funext k
    by_cases hk3 : k = 3 <;> by_cases hk10 : k = 10 <;>
      simp [vertexScanState, Function.update, hk3, hk10, h3]
  rw [hend] at he0
  have hex := OutputExec.seq he3 (OutputExec.seq he2 (OutputExec.seq he1 he0))
  refine ⟨n3+1+(n2+1+(n1+1+n0)), ?_, ?_⟩
  · simpa only [genericColorPass, W0, W1, W2, W3, List.append_assoc] using hex
  · omega

end TensorNP.BilinearEncoder
end


/- Inlined module: GenericMinor -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def genericMinorBody (emitter : OutputCmd) : OutputCmd :=
  .seq (.reg (.assign 19 7)) (.down 19 (countedSelect emitter))

def genericMinorPass (emitter : OutputCmd) : OutputCmd :=
  .seq (.reg (.assign 18 7)) (.down 18 (genericMinorBody emitter))

theorem genericMinorPass_exec (C : ℕ) (data : List BSym) (R : RegFile) (emitter : OutputCmd)
    (N cap B Q : ℕ) (E : ℕ → ℕ → List BSym)
    (h7 : R 7 = N) (h18 : R 18 = 0) (h19 : R 19 = 0)
    (hem : ∀ a b L tail, a < N → b < N → L ≤ cap → ∃ n,
      OutputExec C data emitter (minorScanState R a b L) tail
        (minorScanState R a b L) (E a b ++ tail) n ∧ n ≤ B)
    (hcharge : ∀ a b L, a ≤ N → b ≤ N → L ≤ cap → regCharge (minorScanState R a b L) ≤ Q)
    (hcap : R 10 + scanCount (minorInc N) N ≤ cap) (tail : List BSym) :
    ∃ steps, OutputExec C data (genericMinorPass emitter) R tail
      (Function.update R 10 (R 10 + scanCount (minorInc N) N))
      (scanChunk (fun a => scanChunk (fun b => if a < b then E a b else []) N) N ++ tail) steps ∧
      steps ≤ Q+1+N*((Q+N*(B+2*Q+7)+2)+5)+1 := by
  let word : ℕ → List BSym := fun a => scanChunk (fun b => if a < b then E a b else []) N
  let D := Q+N*(B+2*Q+7)+2
  have hbody : ∀ a L tail', a < N → L + minorInc N a ≤ cap → ∃ n,
      OutputExec C data (genericMinorBody emitter) (minorScanState R a 0 L) tail'
        (minorScanState R a 0 (L + minorInc N a)) (word a ++ tail') n ∧ n ≤ D := by
    intro a L tail' ha hlocal
    have hL : L ≤ cap := by omega
    have hq := hcharge a 0 L (by omega) (by omega) hL
    have haExec : OutputExec C data (.reg (.assign 19 7)) (minorScanState R a 0 L) tail'
        (minorScanState R a N L) tail' (regCharge (minorScanState R a 0 L)) := by
      have he := OutputExec.reg (C := C) tail' (RegExec.assign (data := data) (minorScanState R a 0 L) 19 7)
      simpa only [minorScanState_set19_from7_eq R a 0 L N h7] using he
    have hc' : ∀ b L', b < N → L' ≤ cap → regCharge (minorScanState R a b L') ≤ Q := by
      intro b L' hb hL'
      exact hcharge a b L' (by omega) (by omega) hL'
    have hm : ∀ b L' tail'', b < N → L'+1 ≤ cap → ∃ n,
        OutputExec C data emitter (minorScanState R a b L') tail''
          (minorScanState R a b L') (E a b ++ tail'') n ∧ n ≤ B := by
      intro b L' tail'' hb hL'
      exact hem a b L' tail'' ha hb (by omega)
    obtain ⟨n, he, hn⟩ := filteredScan_exec C data emitter (fun b L' => minorScanState R a b L')
      (E a) a N B Q cap
      (fun b L' => minorScanState_at18 R a b L')
      (fun b L' => minorScanState_at19 R a b L')
      (fun b L' => minorScanState_down19 R a b L')
      (fun b L' => minorScanState_inc10 R a b L') hc' hm N le_rfl L hlocal tail'
    have he' : OutputExec C data (.down 19 (countedSelect emitter)) (minorScanState R a N L) tail'
        (minorScanState R a 0 (L + minorInc N a)) (word a ++ tail') n := by
      simpa only [minorInc, word] using he
    have hex := OutputExec.seq haExec he'
    refine ⟨regCharge (minorScanState R a 0 L)+1+n, hex, ?_⟩
    dsimp [D]
    omega
  have hout := sliceScan_exec C data (genericMinorBody emitter) 18 (fun a L => minorScanState R a 0 L)
    word (minorInc N) N D cap
    (fun a L => minorScanState_at18 R a 0 L)
    (fun a L => minorScanState_down18 R a 0 L) hbody N le_rfl (R 10) hcap tail
  obtain ⟨n, he, hn⟩ := hout
  have hstart : Function.update R 18 (R 7) = minorScanState R N 0 (R 10) := by
    funext k
    by_cases hk18 : k = 18 <;> by_cases hk19 : k = 19 <;> by_cases hk10 : k = 10 <;>
      simp [minorScanState, Function.update, hk18, hk19, hk10, h7, h19]
  have hend : minorScanState R 0 0 (R 10 + scanCount (minorInc N) N) =
      Function.update R 10 (R 10 + scanCount (minorInc N) N) := by
    funext k
    by_cases hk18 : k = 18 <;> by_cases hk19 : k = 19 <;> by_cases hk10 : k = 10 <;>
      simp [minorScanState, Function.update, hk18, hk19, hk10, h18, h19]
  have hassign := OutputExec.reg (C := C) tail (RegExec.assign (data := data) R 18 7)
  rw [hstart] at hassign
  rw [hend] at he
  have hex := OutputExec.seq hassign he
  have hR : regCharge R ≤ Q := by
    have hzero : minorScanState R 0 0 (R 10) = R := by
      funext k
      by_cases hk18 : k = 18 <;> by_cases hk19 : k = 19 <;> by_cases hk10 : k = 10 <;>
        simp [minorScanState, Function.update, hk18, hk19, hk10, h18, h19]
    have h := hcharge 0 0 (R 10) (by omega) (by omega) (by omega)
    simpa only [hzero] using h
  refine ⟨regCharge R+1+n, ?_, ?_⟩
  · simpa only [genericMinorPass, word] using hex
  · dsimp [D] at hn
    omega

end TensorNP.BilinearEncoder
end


/- Inlined module: GenericPass -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def genericSlicePass (minorEmitter : OutputCmd) (colorEmitters : Fin 4 → OutputCmd) : OutputCmd :=
  .seq (genericColorPass colorEmitters) (genericMinorPass minorEmitter)

private theorem minorScanState_update10 (R : RegFile) (t a b L : ℕ) :
    minorScanState (Function.update R 10 t) a b L = minorScanState R a b L := by
  funext k
  by_cases hk18 : k = 18 <;> by_cases hk19 : k = 19 <;> by_cases hk10 : k = 10 <;>
    simp [minorScanState, Function.update, hk18, hk19, hk10]

theorem genericSlicePass_exec (C : ℕ) (data : List BSym) (R : RegFile)
    (minorEmitter : OutputCmd) (colorEmitters : Fin 4 → OutputCmd)
    (v N cap B Q : ℕ) (MW : ℕ → ℕ → List BSym) (CW : Fin 4 → ℕ → List BSym)
    (h0 : R 0 = v) (h3 : R 3 = 0) (h7 : R 7 = N) (h18 : R 18 = 0) (h19 : R 19 = 0)
    (hemMinor : ∀ a b L tail, a < N → b < N → L ≤ cap → ∃ n,
      OutputExec C data minorEmitter (minorScanState R a b L) tail
        (minorScanState R a b L) (MW a b ++ tail) n ∧ n ≤ B)
    (hchargeMinor : ∀ a b L, a ≤ N → b ≤ N → L ≤ cap → regCharge (minorScanState R a b L) ≤ Q)
    (hemColor : ∀ f i L tail, i < v → L ≤ cap → ∃ n,
      OutputExec C data (colorEmitters f) (vertexScanState R i L) tail
        (vertexScanState R i L) (CW f i ++ tail) n ∧ n ≤ B)
    (hchargeColor : ∀ i L, i ≤ v → L ≤ cap → regCharge (vertexScanState R i L) ≤ Q)
    (hcap : R 10+4*v+scanCount (minorInc N) N ≤ cap) (tail : List BSym) :
    ∃ steps, OutputExec C data (genericSlicePass minorEmitter colorEmitters) R tail
      (Function.update R 10 (R 10+4*v+scanCount (minorInc N) N))
      ((scanChunk (fun a => scanChunk (fun b => if a < b then MW a b else []) N) N ++
        (scanChunk (CW 0) v ++ scanChunk (CW 1) v ++ scanChunk (CW 2) v ++ scanChunk (CW 3) v)) ++ tail) steps ∧
      steps ≤ (4*(Q+1+v*(B+Q+6)+1)+3)+1+(Q+1+N*((Q+N*(B+2*Q+7)+2)+5)+1) := by
  let T := Function.update R 10 (R 10+4*v)
  obtain ⟨c, hec, hbc⟩ := genericColorPass_exec C data R colorEmitters CW v cap B Q h0 h3
    hemColor hchargeColor (by omega) tail
  have h7' : T 7 = N := by simpa [T] using h7
  have h18' : T 18 = 0 := by simpa [T] using h18
  have h19' : T 19 = 0 := by simpa [T] using h19
  have hem' : ∀ a b L tail', a < N → b < N → L ≤ cap → ∃ n,
      OutputExec C data minorEmitter (minorScanState T a b L) tail'
        (minorScanState T a b L) (MW a b ++ tail') n ∧ n ≤ B := by
    intro a b L tail' ha hb hL
    simpa only [T, minorScanState_update10] using hemMinor a b L tail' ha hb hL
  have hcharge' : ∀ a b L, a ≤ N → b ≤ N → L ≤ cap → regCharge (minorScanState T a b L) ≤ Q := by
    intro a b L ha hb hL
    simpa only [T, minorScanState_update10] using hchargeMinor a b L ha hb hL
  have hcap' : T 10+scanCount (minorInc N) N ≤ cap := by simpa [T] using hcap
  obtain ⟨m, hem, hbm⟩ := genericMinorPass_exec C data T minorEmitter N cap B Q MW
    h7' h18' h19' hem' hcharge' hcap'
    ((scanChunk (CW 0) v ++ scanChunk (CW 1) v ++ scanChunk (CW 2) v ++ scanChunk (CW 3) v) ++ tail)
  have hend : Function.update T 10 (T 10+scanCount (minorInc N) N) =
      Function.update R 10 (R 10+4*v+scanCount (minorInc N) N) := by simp [T]
  rw [hend] at hem
  have hex := OutputExec.seq hec hem
  refine ⟨c+1+m, ?_, ?_⟩
  · simpa only [genericSlicePass, List.append_assoc] using hex
  · omega

end TensorNP.BilinearEncoder
end


/- Inlined module: RealBody -/
section
-- Actual source body: RealBudget

set_option autoImplicit false
namespace TensorNP.BilinearEncoder

def realMatrixBudget (C size N : ℕ) : ℕ :=
  100*(size+1)+1+((N+N)*(100*(size+(N+N)+1)+
    (N+N)*(10^20*(C+1)*(size+N+2)^4+5)+7)+1)

def realPassBudget (C size v cap : ℕ) : ℕ :=
  let N := 2*v+1
  let S := size+2*N+v+3*cap
  let Q := 100*(S+1)
  let M := realMatrixBudget C S N
  let Pcolor := 4*(Q+1+v*(M+Q+6)+1)+3
  let Pminor := Q+1+N*((Q+N*(M+2*Q+7)+2)+5)+1
  Pcolor+1+Pminor

theorem realPassBudget_mono (C v : ℕ) {size size' cap cap' : ℕ}
    (hs : size ≤ size') (hc : cap ≤ cap') :
    realPassBudget C size v cap ≤ realPassBudget C size' v cap' := by
  dsimp [realPassBudget, realMatrixBudget]
  gcongr

theorem realPassBudget_le (C size v cap : ℕ)
    (hs : size ≤ 100*(v+1)^2) (hc : cap ≤ 100*(v+1)^2) :
    realPassBudget C size v cap ≤ 10^70*(C+1)*(v+1)^16 := by
  let X := (v+1)^2
  have hsquare : v+1 ≤ (v+1)^2 := Nat.le_self_pow (by decide) _
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hv : v ≤ X := by dsimp [X]; omega
  have hmono : realPassBudget C size v cap ≤ realPassBudget C (100*X) X (100*X) := by
    dsimp [realPassBudget, realMatrixBudget]
    gcongr
  have hp (k : ℕ) (hk : k ≤ 8) : (C+1)*X^k ≤ (C+1)*X^8 :=
    Nat.mul_le_mul_left (C+1) (pow_le_pow_right₀ hx hk)
  have hz (k : ℕ) : X^k ≤ (C+1)*X^k := by
    simpa using Nat.mul_le_mul_right (X^k) (show 1 ≤ C+1 by omega)
  have hbound : realPassBudget C (100*X) X (100*X) ≤ 10^70*(C+1)*X^8 := by
    have h0 := hp 0 (by omega)
    have h1 := hp 1 (by omega)
    have h2 := hp 2 (by omega)
    have h3 := hp 3 (by omega)
    have h4 := hp 4 (by omega)
    have h5 := hp 5 (by omega)
    have h6 := hp 6 (by omega)
    have h7 := hp 7 (by omega)
    have z0 := hz 0
    have z1 := hz 1
    have z2 := hz 2
    have z3 := hz 3
    have z4 := hz 4
    have z5 := hz 5
    have z6 := hz 6
    have z7 := hz 7
    dsimp [realPassBudget, realMatrixBudget]
    nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, z0, z1, z2, z3, z4, z5, z6, z7]
  calc
    _ ≤ realPassBudget C (100*X) X (100*X) := hmono
    _ ≤ 10^70*(C+1)*X^8 := hbound
    _ = 10^70*(C+1)*(v+1)^16 := by dsimp [X]; ring

end TensorNP.BilinearEncoder

                                                          
                                                        

-- Actual source body: RealPass

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def realPass (high : Bool) : OutputCmd :=
  genericSlicePass (matrixProgram (matrixEntry (realCoefficient high minorProgram)))
    (fun f => matrixProgram (matrixEntry (realCoefficient high (colorFamily f))))

def realMinorWord (high : Bool) (N a b : ℕ) : List BSym :=
  sliceValueWord (some high) N (minorValue a b)

def realColorWord (high : Bool) (v N : ℕ) (data : List BSym) (f : Fin 4) (i : ℕ) : List BSym :=
  sliceValueWord (some high) N (colorValue v data f.val i)

private theorem realMatrixBudget_size_mono (C N : ℕ) {s t : ℕ} (h : s ≤ t) :
    realMatrixBudget C s N ≤ realMatrixBudget C t N := by
  unfold realMatrixBudget
  gcongr

private theorem realMatrixBound_eq_budget (C s N : ℕ) : realMatrixBound C s N = realMatrixBudget C s N := by
  norm_num [realMatrixBound, realMatrixBudget]

theorem passWord_some_eq (high : Bool) (v : ℕ) (data : List BSym) :
    passWord (some high) v data =
      scanChunk (fun a => scanChunk (fun b => if a < b then realMinorWord high (2*v+1) a b else []) (2*v+1)) (2*v+1) ++
        (scanChunk (realColorWord high v (2*v+1) data 0) v ++ scanChunk (realColorWord high v (2*v+1) data 1) v ++
          scanChunk (realColorWord high v (2*v+1) data 2) v ++ scanChunk (realColorWord high v (2*v+1) data 3) v) := by
  have h4 (f : ℕ → List BSym) :
      (List.range 4).flatMap f = f 0 ++ f 1 ++ f 2 ++ f 3 := by
    simp [List.range_succ, List.append_assoc]
  simp only [passWord, scanChunk, h4, List.append_assoc]
  rfl

theorem realPass_exec (C : ℕ) (data : List BSym) (R : RegFile) (high : Bool)
    (v N cap : ℕ) (hN : N = 2*v+1) (h0 : R 0 = v) (hlen : data.length = v*v)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h3 : R 3 = 0) (h4 : R 4 = 0) (h8 : R 8 = 0) (h9 : R 9 = 0)
    (h12 : R 12 = 0) (h13 : R 13 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) (h16 : R 16 = 0)
    (h18 : R 18 = 0) (h19 : R 19 = 0) (h7 : R 7 = N) (h6 : R 6 = N+N)
    (hcap : R 10+4*v+scanCount (minorInc N) N ≤ cap) (tail : List BSym) :
    ∃ steps, OutputExec C data (realPass high) R tail
      (Function.update R 10 (R 10+4*v+scanCount (minorInc N) N))
      (passWord (some high) v data ++ tail) steps ∧ steps ≤ realPassBudget C (regSize R) v cap := by
  let S := regSize R+2*N+v+3*cap
  let Q := 100*(S+1)
  let M := realMatrixBudget C S N
  let em := matrixProgram (matrixEntry (realCoefficient high minorProgram))
  let ec : Fin 4 → OutputCmd := fun f => matrixProgram (matrixEntry (realCoefficient high (colorFamily f)))
  have hchargeMinor : ∀ a b L, a ≤ N → b ≤ N → L ≤ cap → regCharge (minorScanState R a b L) ≤ Q := by
    intro a b L ha hb hL
    have hs := minorScanState_size R a b L
    dsimp [Q, S, regCharge]
    omega
  have hchargeColor : ∀ i L, i ≤ v → L ≤ cap → regCharge (vertexScanState R i L) ≤ Q := by
    intro i L hi hL
    have hs := vertexScanState_size R i L
    dsimp [Q, S, regCharge]
    omega
  have hemMinor : ∀ a b L tail', a < N → b < N → L ≤ cap → ∃ n,
      OutputExec C data em (minorScanState R a b L) tail' (minorScanState R a b L)
        (realMinorWord high N a b ++ tail') n ∧ n ≤ M := by
    intro a b L tail' ha hb hL
    let T := minorScanState R a b L
    have h1' : T 1 = 0 := by simpa [T, minorScanState] using h1
    have h2' : T 2 = 0 := by simpa [T, minorScanState] using h2
    have h14' : T 14 = 0 := by simpa [T, minorScanState] using h14
    have h15' : T 15 = 0 := by simpa [T, minorScanState] using h15
    have h16' : T 16 = 0 := by simpa [T, minorScanState] using h16
    have h7' : T 7 = N := by simpa [T, minorScanState] using h7
    have h6' : T 6 = N+N := by simpa [T, minorScanState] using h6
    have h12' : T 12 = 0 := by simpa [T, minorScanState] using h12
    have h13' : T 13 = 0 := by simpa [T, minorScanState] using h13
    obtain ⟨n, he, hn⟩ := realMinorMatrix_exec C data T N high h1' h2' h14' h15' h16' h7' h6' h12' h13' tail'
    have hword : realMinorEntryWord high N a b =
        (fun row col => TensorNP.Eigen.encRat (realEntryValue high N (minorValue a b) row col)) := rfl
    refine ⟨n, ?_, ?_⟩
    · simpa only [em, T, minorScanState_at18, minorScanState_at19, realMinorWord,
        sliceValueWord, matrixValueWord, hword] using he
    · have hs : regSize T ≤ S := by
        have hs' := minorScanState_size R a b L
        dsimp [T, S] at *
        omega
      have hb := realMatrixBudget_size_mono C N hs
      rw [realMatrixBound_eq_budget] at hn
      exact hn.trans hb
  have hemColor : ∀ f i L tail', i < v → L ≤ cap → ∃ n,
      OutputExec C data (ec f) (vertexScanState R i L) tail' (vertexScanState R i L)
        (realColorWord high v N data f i ++ tail') n ∧ n ≤ M := by
    intro f i L tail' hi hL
    let T := vertexScanState R i L
    have h0' : T 0 = v := by simpa [T, vertexScanState] using h0
    have h3' : T 3 = i := by simp [T]
    have hlen' : data.length = T 0*T 0 := by simpa [h0'] using hlen
    have h1' : T 1 = 0 := by simpa [T, vertexScanState] using h1
    have h2' : T 2 = 0 := by simpa [T, vertexScanState] using h2
    have h4' : T 4 = 0 := by simpa [T, vertexScanState] using h4
    have h8' : T 8 = 0 := by simpa [T, vertexScanState] using h8
    have h9' : T 9 = 0 := by simpa [T, vertexScanState] using h9
    have h14' : T 14 = 0 := by simpa [T, vertexScanState] using h14
    have h15' : T 15 = 0 := by simpa [T, vertexScanState] using h15
    have h16' : T 16 = 0 := by simpa [T, vertexScanState] using h16
    have h7' : T 7 = N := by simpa [T, vertexScanState] using h7
    have h6' : T 6 = N+N := by simpa [T, vertexScanState] using h6
    have h12' : T 12 = 0 := by simpa [T, vertexScanState] using h12
    have h13' : T 13 = 0 := by simpa [T, vertexScanState] using h13
    obtain ⟨n, he, hn⟩ := realColorMatrix_exec C data T N high f hlen' (by omega)
      h1' h2' h4' h8' h9' h14' h15' h16' h7' h6' h12' h13' tail'
    have hword : realColorEntryWord high N v data f.val i =
        (fun row col => TensorNP.Eigen.encRat (realEntryValue high N (colorValue v data f.val i) row col)) := rfl
    rw [h0', h3'] at he
    refine ⟨n, ?_, ?_⟩
    · simpa only [ec, T, realColorWord, sliceValueWord, matrixValueWord, hword] using he
    · have hs : regSize T ≤ S := by
        have hs' := vertexScanState_size R i L
        dsimp [T, S] at *
        omega
      have hb := realMatrixBudget_size_mono C N hs
      rw [realMatrixBound_eq_budget] at hn
      exact hn.trans hb
  obtain ⟨n, he, hn⟩ := genericSlicePass_exec C data R em ec v N cap M Q
    (realMinorWord high N) (realColorWord high v N data) h0 h3 h7 h18 h19
    hemMinor hchargeMinor hemColor hchargeColor hcap tail
  refine ⟨n, ?_, ?_⟩
  · subst N
    simpa only [realPass, em, ec, passWord_some_eq] using he
  · subst N
    simpa only [realPassBudget, S, Q, M] using hn

end TensorNP.BilinearEncoder
                                                       
                                                    

-- Actual source body: RealBodyCore

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def realPasses : OutputCmd := .seq (realPass true) (realPass false)

theorem realPasses_exec (C : ℕ) (data : List BSym) (R : RegFile)
    (v N cap : ℕ) (hN : N = 2*v+1) (h0 : R 0 = v) (hlen : data.length = v*v)
    (h1 : R 1 = 0) (h2 : R 2 = 0) (h3 : R 3 = 0) (h4 : R 4 = 0)
    (h8 : R 8 = 0) (h9 : R 9 = 0) (h12 : R 12 = 0) (h13 : R 13 = 0)
    (h14 : R 14 = 0) (h15 : R 15 = 0) (h16 : R 16 = 0)
    (h18 : R 18 = 0) (h19 : R 19 = 0) (h7 : R 7 = N) (h6 : R 6 = N+N)
    (hcap : R 10+(4*v+scanCount (minorInc N) N)+(4*v+scanCount (minorInc N) N) ≤ cap)
    (tail : List BSym) :
    ∃ steps, OutputExec C data realPasses R tail
      (Function.update R 10 (R 10+(4*v+scanCount (minorInc N) N)+(4*v+scanCount (minorInc N) N)))
      (passWord (some false) v data ++ passWord (some true) v data ++ tail) steps ∧
      steps ≤ realPassBudget C (regSize R) v cap+1+
        realPassBudget C (regSize (Function.update R 10 (R 10+4*v+scanCount (minorInc N) N))) v cap := by
  obtain ⟨a, ha, hab⟩ := realPass_exec C data R true v N cap hN h0 hlen
    h1 h2 h3 h4 h8 h9 h12 h13 h14 h15 h16 h18 h19 h7 h6 (by omega) tail
  let H := Function.update R 10 (R 10+4*v+scanCount (minorInc N) N)
  obtain ⟨b, hb, hbb⟩ := realPass_exec C data H false v N cap hN
    (by simpa [H] using h0) hlen
    (by simpa [H] using h1) (by simpa [H] using h2) (by simpa [H] using h3)
    (by simpa [H] using h4) (by simpa [H] using h8) (by simpa [H] using h9)
    (by simpa [H] using h12) (by simpa [H] using h13) (by simpa [H] using h14)
    (by simpa [H] using h15) (by simpa [H] using h16) (by simpa [H] using h18)
    (by simpa [H] using h19) (by simpa [H] using h7) (by simpa [H] using h6)
    (by simpa [H, Nat.add_assoc] using hcap)
    (passWord (some true) v data ++ tail)
  have he := OutputExec.seq ha hb
  refine ⟨a+1+b, ?_, ?_⟩
  · simpa [realPasses, H, Nat.add_assoc, List.append_assoc] using he
  · exact Nat.add_le_add (Nat.add_le_add_right hab 1) hbb

end TensorNP.BilinearEncoder
end


/- Inlined module: RealBodyLayout -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def realBodyRegs (v : ℕ) : RegFile :=
  Function.update (dimensionState true (encoderRegs v)) 10 (complexSlices v + complexSlices v)

def realBodyWord (v : ℕ) (data : List BSym) : List BSym :=
  if v = 0 then matrixValueWord (minorValue 0 0) 2 ++ matrixValueWord (minorValue 0 0) 2
  else passWord (some false) v data ++ passWord (some true) v data

theorem realBody_header (v : ℕ) (data : List BSym) :
    encNats [(realBodyRegs v) 10, (realBodyRegs v) 6, (realBodyRegs v) 6] ++ realBodyWord v data =
      realPayload v data := by
  cases v with
  | zero => simp [realBodyRegs, realBodyWord, dimensionState, encoderRegs, realPayload, complexSlices]
  | succ v => simp [realBodyRegs, realBodyWord, dimensionState, encoderRegs, realPayload, complexSlices]

theorem complexSlices_bound (v : ℕ) : complexSlices v ≤ 7*(v+1)^2 := by
  cases v with
  | zero => simp [complexSlices]
  | succ v => simp only [complexSlices]; nlinarith

theorem realBodyRegs_size (v : ℕ) : regSize (realBodyRegs v) + 1 ≤ 30*(v+1)^2 := by
  obtain ⟨hs, hd, hu⟩ := And.intro (complexSlices_bound v)
    (And.intro (dimensionState_encoderRegs_size true v)
      (regSize_update_le (dimensionState true (encoderRegs v)) 10 (complexSlices v + complexSlices v)))
  have hl : v + 1 ≤ (v + 1)^2 := Nat.le_self_pow (by decide) _
  change regSize (realBodyRegs v) ≤ _ at hu
  omega

theorem real_two_slices_cap (v : ℕ) :
    complexSlices v + complexSlices v ≤ 100*(v+1)^2 := by
  have h := complexSlices_bound v
  omega

theorem real_mid_size (v : ℕ) :
    regSize (Function.update (dimensionState true (encoderRegs v)) 10 (complexSlices v)) ≤
      100*(v+1)^2 := by
  have hs := complexSlices_bound v
  have hd := dimensionState_encoderRegs_size true v
  have hu := regSize_update_le (dimensionState true (encoderRegs v)) 10 (complexSlices v)
  have hl : v + 1 ≤ (v + 1)^2 := Nat.le_self_pow (by decide) _
  omega

end TensorNP.BilinearEncoder
end


/- Inlined module: RealEncoder -/
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder
namespace TensorNP.BilinearEncoder

def realBody : OutputCmd :=
  .seq (.reg (dimensionInit true)) (.branch false 0 1 zeroDouble realPasses)

private theorem realEncoder_complexSlices_pos (v : ℕ) (hv : v ≠ 0) :
    complexSlices v = v*(2*v+5) := by
  cases v with
  | zero => contradiction
  | succ v => rfl

theorem realBody_exec (C : ℕ) (data : List BSym) (v : ℕ) (hlen : data.length = v*v) :
    ∃ steps, OutputExec C data realBody (encoderRegs v) [] (realBodyRegs v)
      (realBodyWord v data) steps ∧ steps ≤ 10^80*(C+1)*(v+1)^16 := by
  let S := dimensionState true (encoderRegs v)
  have hf : S 0 = v ∧ S 1 = 0 ∧ S 2 = 0 ∧ S 3 = 0 ∧ S 4 = 0 ∧
      S 8 = 0 ∧ S 9 = 0 ∧ S 10 = 0 ∧ S 12 = 0 ∧ S 13 = 0 ∧
      S 14 = 0 ∧ S 15 = 0 ∧ S 16 = 0 ∧ S 18 = 0 ∧ S 19 = 0 ∧
      S 7 = 2*v+1 ∧ S 6 = (2*v+1)+(2*v+1) := by
    simp [S, dimensionState, encoderRegs]
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs8, hs9, hs10, hs12, hs13, hs14, hs15, hs16, hs18, hs19, hs7, hs6⟩ := hf
  have hsize : regSize S ≤ 10*(v+1) := dimensionState_encoderRegs_size true v
  have hsize' : regSize S ≤ 100*(v+1)^2 := by
    have hl : v+1 ≤ (v+1)^2 := Nat.le_self_pow (by decide) _
    omega
  obtain ⟨n, hn, hnb⟩ := dimensionInit_exec true data (encoderRegs v)
  have hbranch : ∃ m, OutputExec C data (.branch false 0 1 zeroDouble realPasses)
      S [] (realBodyRegs v) (realBodyWord v data) m ∧
      m ≤ regCharge S + 10^75*(C+1)*(v+1)^16 := by
    by_cases hv : v = 0
    · have hguard : regCompare false 0 1 S = true := by simp [regCompare, hs0, hs1, hv]
      obtain ⟨m, hm, hmb⟩ := zeroDouble_exec C data S 2 hs18 hs19 hs1 hs2 hs12 hs13
        hs14 hs15 (by simpa [hv] using hs6) []
      have hz : OutputExec C data zeroDouble S [] (realBodyRegs v) (realBodyWord v data) m := by
        change OutputExec C data zeroDouble S [] (Function.update S 10 (complexSlices v + complexSlices v))
          (if v = 0 then matrixValueWord (minorValue 0 0) 2 ++ matrixValueWord (minorValue 0 0) 2
           else passWord (some false) v data ++ passWord (some true) v data) m
        simp only [hv, complexSlices, if_true]
        simpa only [hs10, zero_add, List.append_nil] using hm
      have he : OutputExec C data (.branch false 0 1 zeroDouble realPasses)
          S [] (realBodyRegs v) (realBodyWord v data) (regCharge S+m) := by
        apply OutputExec.branch (R := S) (T := realBodyRegs v) (n := m)
        rw [hguard]
        exact hz
      refine ⟨_, he, ?_⟩
      have hm' := minorMatrixBound_mono C 2 (show regSize S + S 10 + 2 ≤ 12 by
        have hs : regSize S ≤ 10 := by simpa [hv] using hsize
        omega)
      have hm'' : minorMatrixBound C (regSize S + S 10 + 2) 2 ≤ 102400000000*(C+1)+4336 := by
        calc
          _ ≤ minorMatrixBound C 12 2 := hm'
          _ = _ := by simp [minorMatrixBound]; ring
      simp only [hv, Nat.zero_add, one_pow, Nat.mul_one]
      simp only [hv, Nat.zero_add, Nat.mul_one] at hsize
      omega
    · let cap := 100*(v+1)^2
      have hcount : 4*v + scanCount (minorInc (2*v+1)) (2*v+1) = complexSlices v := by
        have h := minorSliceCount v
        rw [realEncoder_complexSlices_pos v hv]
        omega
      have hcap : S 10 + (4*v + scanCount (minorInc (2*v+1)) (2*v+1)) +
          (4*v + scanCount (minorInc (2*v+1)) (2*v+1)) ≤ cap := by
        simpa [hs10, hcount, cap] using real_two_slices_cap v
      obtain ⟨m, hm, hmb⟩ := realPasses_exec C data S v (2*v+1) cap rfl hs0 hlen
        hs1 hs2 hs3 hs4 hs8 hs9 hs12 hs13 hs14 hs15 hs16 hs18 hs19 hs7 hs6 hcap []
      have hmid : regSize (Function.update S 10 (S 10+4*v+scanCount (minorInc (2*v+1)) (2*v+1))) ≤
          100*(v+1)^2 := by
        simpa [S, hs10, Nat.add_assoc, hcount] using real_mid_size v
      have hz : OutputExec C data realPasses S [] (realBodyRegs v) (realBodyWord v data) m := by
        simpa [realBodyRegs, realBodyWord, hv, hs10, hcount, S] using hm
      have hguard : regCompare false 0 1 S = false := by simp [regCompare, hs0, hs1, hv]
      have he : OutputExec C data (.branch false 0 1 zeroDouble realPasses)
          S [] (realBodyRegs v) (realBodyWord v data) (regCharge S+m) := by
        apply OutputExec.branch (R := S) (T := realBodyRegs v) (n := m)
        rw [hguard]
        exact hz
      have hb1 := realPassBudget_le C (regSize S) v cap hsize' (by dsimp [cap]; rfl)
      have hb2 := realPassBudget_le C _ v cap hmid (by dsimp [cap]; rfl)
      have hprod : 1 ≤ (C+1)*(v+1)^16 := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
      refine ⟨_, he, ?_⟩
      simp only [Nat.mul_assoc] at *
      omega
  obtain ⟨m, hm, hmb⟩ := hbranch
  refine ⟨n+1+m, ?_, ?_⟩
  · exact OutputExec.seq (OutputExec.reg [] hn) hm
  · have hp16 : v+1 ≤ (v+1)^16 := Nat.le_self_pow (by decide) _
    have hprod : (v+1)^16 ≤ (C+1)*(v+1)^16 := Nat.le_mul_of_pos_left _ (by omega)
    simp only [regCharge] at hmb
    simp only [encoderRegs_size] at hnb
    simp only [Nat.mul_assoc] at hmb ⊢
    omega

theorem real_payload_poly : CookPvsNP.PolyTimeComputable (graphEncoderValue realPayload) := by
  apply graph_payload_poly_of_output realPayload realBody 16
  intro C
  refine ⟨10^85*(C+1), ?_⟩
  intro v G
  have hlen : (graphData G).length = v*v := by simpa [graphData] using (graphBits_valid G).1
  obtain ⟨n, he, hn⟩ := realBody_exec C (graphData G) v hlen
  refine ⟨realBodyRegs v, realBodyWord v (graphData G), n, he, ?_, ?_, ?_⟩
  · simp only [Nat.mul_assoc] at hn ⊢
    omega
  · have hs := realBodyRegs_size v
    have hp : (v+1)^2 ≤ (v+1)^16 := pow_le_pow_right₀ (by omega) (by omega)
    have hprod : (v+1)^16 ≤ (C+1)*(v+1)^16 := Nat.le_mul_of_pos_left _ (by omega)
    simp only [Nat.mul_assoc]
    omega
  · exact realBody_header v (graphData G)

end TensorNP.BilinearEncoder
end


/- Inlined module: MainDraft -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Encoder

open TensorNP.BilinearEncoder

/-- Exact mission target using the four proved encoder obligations. -/
theorem solution :
    PolyReducible TensorNP.Eigen.threeColLang (TensorNP.Bilinear.tbfLang ℝ) ∧
    PolyReducible TensorNP.Eigen.threeColLang (TensorNP.Bilinear.tbfLang ℂ) := by
  exact ⟨graph_payload_reduction ℝ realPayload real_payload_poly
      (fun v G => by simpa only [real_payload_code] using realTensor_code_mem_iff G),
    graph_payload_reduction ℂ complexPayload complex_payload_poly
      (fun v G => by simpa only [complex_payload_code] using complexTensor_code_mem_iff G)⟩
end
