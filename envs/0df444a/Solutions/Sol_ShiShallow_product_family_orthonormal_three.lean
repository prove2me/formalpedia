-- Prove2me | solution 1 for ShiShallow.product_family_orthonormal_three
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T03:42:23.622632+00:00
-- url     : https://prove2.me/submissions/fa4835f1-6bd2-41a5-98a4-fcb6cbc4e37c

import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

open ShiShallow ShiTensor

/-! ### Private infrastructure

`y ↦ (leftBits y, rightBits y)` is a bijection `Bits (m + p) ≃ Bits m × Bits p`, with inverse
`Fin.append`.  This is exactly the reindexing fact that `Def_ShiTensor_Core` deliberately omits
(limitation 2 of its module docstring), so it is established here from scratch.

The three-block case is obtained by iterating the two-block case on the LEFT factor: since
`Bits (m + p + q)` is `Bits ((m + p) + q)`, the outer split is `(m + p)` against `q`, and the
left half is split again into `m` against `p`.  No associativity reindexing is required. -/

private lemma bits_bijective (m p : ℕ) :
    Function.Bijective (fun y : Bits (m + p) => (leftBits y, rightBits y)) := by
  constructor
  · intro y z h
    have h1 : leftBits (m := m) (p := p) y = leftBits z :=
      congrArg (fun q : Bits m × Bits p => q.1) h
    have h2 : rightBits (m := m) (p := p) y = rightBits z :=
      congrArg (fun q : Bits m × Bits p => q.2) h
    have e1 : Fin.append (leftBits (m := m) (p := p) y) (rightBits (m := m) (p := p) y) = y :=
      Fin.append_castAdd_natAdd
    have e2 : Fin.append (leftBits (m := m) (p := p) z) (rightBits (m := m) (p := p) z) = z :=
      Fin.append_castAdd_natAdd
    calc y
        = Fin.append (leftBits (m := m) (p := p) y) (rightBits (m := m) (p := p) y) := e1.symm
      _ = Fin.append (leftBits (m := m) (p := p) z) (rightBits (m := m) (p := p) z) := by
            rw [h1, h2]
      _ = z := e2
  · rintro ⟨a, b⟩
    refine ⟨Fin.append a b, ?_⟩
    have h1 : leftBits (m := m) (p := p) (Fin.append a b) = a := by
      funext i
      first
        | exact Fin.append_left a b i
        | (simp only [leftBits, Fin.append_left]; done)
    have h2 : rightBits (m := m) (p := p) (Fin.append a b) = b := by
      funext j
      first
        | exact Fin.append_right a b j
        | (simp only [rightBits, Fin.append_right]; done)
    simp only [h1, h2]

/-- Sum factorisation over a split index. -/
private lemma sum_split {m p : ℕ} (f : Bits m → ℂ) (g : Bits p → ℂ) :
    (∑ y : Bits (m + p), f (leftBits y) * g (rightBits y))
      = (∑ a : Bits m, f a) * ∑ b : Bits p, g b := by
  have h1 : (∑ y : Bits (m + p), f (leftBits y) * g (rightBits y))
      = ∑ x : Bits m × Bits p, f x.1 * g x.2 :=
    Fintype.sum_bijective _ (bits_bijective m p)
      (fun y : Bits (m + p) => f (leftBits y) * g (rightBits y))
      (fun x : Bits m × Bits p => f x.1 * g x.2) (fun _ => rfl)
  have h2 : (∑ x : Bits m × Bits p, f x.1 * g x.2)
      = ∑ a : Bits m, ∑ b : Bits p, f a * g b :=
    Fintype.sum_prod_type (fun x : Bits m × Bits p => f x.1 * g x.2)
  have h3 : ((∑ a : Bits m, f a) * ∑ b : Bits p, g b)
      = ∑ a : Bits m, ∑ b : Bits p, f a * g b :=
    Fintype.sum_mul_sum f g
  calc (∑ y : Bits (m + p), f (leftBits y) * g (rightBits y))
      = ∑ x : Bits m × Bits p, f x.1 * g x.2 := h1
    _ = ∑ a : Bits m, ∑ b : Bits p, f a * g b := h2
    _ = (∑ a : Bits m, f a) * ∑ b : Bits p, g b := h3.symm

/-- The inner product of two split-index products factors as the product of the inner products. -/
private lemma inner_prod_eq {m p : ℕ}
    (a b : EuclideanSpace ℂ (Bits m)) (c d : EuclideanSpace ℂ (Bits p)) :
    inner ℂ
        (WithLp.toLp 2 (fun y : Bits (m + p) => a (leftBits y) * c (rightBits y)) :
          EuclideanSpace ℂ (Bits (m + p)))
        (WithLp.toLp 2 (fun y : Bits (m + p) => b (leftBits y) * d (rightBits y)) :
          EuclideanSpace ℂ (Bits (m + p)))
      = inner ℂ a b * inner ℂ c d := by
  have hA : inner ℂ a b = ∑ x : Bits m, b x * (starRingEnd ℂ) (a x) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply]
  have hC : inner ℂ c d = ∑ x : Bits p, d x * (starRingEnd ℂ) (c x) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply]
  have hAll : inner ℂ
        (WithLp.toLp 2 (fun y : Bits (m + p) => a (leftBits y) * c (rightBits y)) :
          EuclideanSpace ℂ (Bits (m + p)))
        (WithLp.toLp 2 (fun y : Bits (m + p) => b (leftBits y) * d (rightBits y)) :
          EuclideanSpace ℂ (Bits (m + p)))
      = ∑ y : Bits (m + p),
          (b (leftBits y) * (starRingEnd ℂ) (a (leftBits y))) *
            (d (rightBits y) * (starRingEnd ℂ) (c (rightBits y))) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    first
      | (simp only [PiLp.toLp_apply, RCLike.inner_apply, map_mul]; ring; done)
      | (simp only [WithLp.ofLp_toLp, PiLp.toLp_apply, RCLike.inner_apply, map_mul]; ring; done)
      | (simp only [PiLp.toLp_apply, RCLike.inner_apply, map_mul]; done)
      | (simp [PiLp.toLp_apply, RCLike.inner_apply, map_mul]; ring; done)
      | (simp [PiLp.toLp_apply, RCLike.inner_apply, map_mul, mul_comm, mul_assoc,
            mul_left_comm]; done)
  calc inner ℂ
        (WithLp.toLp 2 (fun y : Bits (m + p) => a (leftBits y) * c (rightBits y)) :
          EuclideanSpace ℂ (Bits (m + p)))
        (WithLp.toLp 2 (fun y : Bits (m + p) => b (leftBits y) * d (rightBits y)) :
          EuclideanSpace ℂ (Bits (m + p)))
      = ∑ y : Bits (m + p),
          (b (leftBits y) * (starRingEnd ℂ) (a (leftBits y))) *
            (d (rightBits y) * (starRingEnd ℂ) (c (rightBits y))) := hAll
    _ = (∑ x : Bits m, b x * (starRingEnd ℂ) (a x)) *
          ∑ x : Bits p, d x * (starRingEnd ℂ) (c x) :=
        sum_split (fun x : Bits m => b x * (starRingEnd ℂ) (a x))
          (fun x : Bits p => d x * (starRingEnd ℂ) (c x))
    _ = inner ℂ a b * inner ℂ c d := by rw [hA, hC]

/-- Three-fold version of `inner_prod_eq`, obtained by applying the two-fold version twice: once
for the outer `(m + p)`-against-`q` split, once for the inner `m`-against-`p` split of the left
factor.  The left factor of the outer application is the two-block product vector, whose value at
`leftBits y` is definitionally the product of the two amplitudes (`PiLp.toLp_apply` is `rfl`). -/
private lemma inner_prod_eq_three {m p q : ℕ}
    (a₁ a₂ : EuclideanSpace ℂ (Bits m)) (b₁ b₂ : EuclideanSpace ℂ (Bits p))
    (c₁ c₂ : EuclideanSpace ℂ (Bits q)) :
    inner ℂ
        (WithLp.toLp 2 (fun y : Bits (m + p + q) =>
            a₁ (leftBits (leftBits y)) * b₁ (rightBits (leftBits y)) * c₁ (rightBits y)) :
          EuclideanSpace ℂ (Bits (m + p + q)))
        (WithLp.toLp 2 (fun y : Bits (m + p + q) =>
            a₂ (leftBits (leftBits y)) * b₂ (rightBits (leftBits y)) * c₂ (rightBits y)) :
          EuclideanSpace ℂ (Bits (m + p + q)))
      = inner ℂ a₁ a₂ * inner ℂ b₁ b₂ * inner ℂ c₁ c₂ := by
  have h := inner_prod_eq (m := m + p) (p := q)
      (WithLp.toLp 2 (fun y : Bits (m + p) => a₁ (leftBits y) * b₁ (rightBits y)) :
        EuclideanSpace ℂ (Bits (m + p)))
      (WithLp.toLp 2 (fun y : Bits (m + p) => a₂ (leftBits y) * b₂ (rightBits y)) :
        EuclideanSpace ℂ (Bits (m + p)))
      c₁ c₂
  rw [inner_prod_eq a₁ a₂ b₁ b₂] at h
  first
    | (exact h)
    | (simpa only [PiLp.toLp_apply] using h)
    | (rw [← h]; done)
    | (simp only [PiLp.toLp_apply] at h ⊢; exact h)

/-- Products of three orthonormal families, indexed along the left-nested split
`(Bits m × Bits p) × Bits q` of the wires, form an orthonormal family on the joint register. -/
theorem solution {m p q : ℕ}
    (u : Bits m → EuclideanSpace ℂ (Bits m)) (v : Bits p → EuclideanSpace ℂ (Bits p))
    (w : Bits q → EuclideanSpace ℂ (Bits q))
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w) :
    Orthonormal ℂ (fun i : (Bits m × Bits p) × Bits q =>
      (WithLp.toLp 2 (fun y : Bits (m + p + q) =>
          u i.1.1 (leftBits (leftBits y)) * v i.1.2 (rightBits (leftBits y))
            * w i.2 (rightBits y)) : EuclideanSpace ℂ (Bits (m + p + q)))) := by
  rw [orthonormal_iff_ite] at hu hv hw
  refine orthonormal_iff_ite.mpr ?_
  intro i j
  show inner ℂ
      (WithLp.toLp 2 (fun y : Bits (m + p + q) =>
          u i.1.1 (leftBits (leftBits y)) * v i.1.2 (rightBits (leftBits y))
            * w i.2 (rightBits y)) : EuclideanSpace ℂ (Bits (m + p + q)))
      (WithLp.toLp 2 (fun y : Bits (m + p + q) =>
          u j.1.1 (leftBits (leftBits y)) * v j.1.2 (rightBits (leftBits y))
            * w j.2 (rightBits y)) : EuclideanSpace ℂ (Bits (m + p + q)))
      = if i = j then (1 : ℂ) else 0
  rw [inner_prod_eq_three (u i.1.1) (u j.1.1) (v i.1.2) (v j.1.2) (w i.2) (w j.2), hu, hv, hw]
  rcases eq_or_ne i j with h | h
  · subst h
    simp
  · rw [if_neg h]
    have hne : ¬ ((i.1.1 = j.1.1 ∧ i.1.2 = j.1.2) ∧ i.2 = j.2) := by
      intro hc
      exact h (Prod.ext_iff.mpr ⟨Prod.ext_iff.mpr hc.1, hc.2⟩)
    rcases not_and_or.mp hne with h1 | h1
    · rcases not_and_or.mp h1 with h2 | h2
      · rw [if_neg h2, zero_mul, zero_mul]
      · rw [if_neg h2, mul_zero, zero_mul]
    · rw [if_neg h1, mul_zero]
