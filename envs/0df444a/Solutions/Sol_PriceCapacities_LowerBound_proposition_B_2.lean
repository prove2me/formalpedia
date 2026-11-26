-- Prove2me | solution 1 for PriceCapacities.LowerBound.proposition_B_2
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T07:53:25.947923+00:00
-- url     : https://prove2.me/submissions/286554fa-7165-41bb-9f42-23a043cff378

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_Fourier

open PriceCapacities PriceCapacities.LowerBound

namespace P2MHole01_de946156
theorem solution {d : ℕ} (f : Cube d → ℝ) : ∑ y : Cube d, f (-y) = ∑ y : Cube d, f y := by
  have hinj : Set.InjOn (fun y : Cube d => -y) (Finset.univ : Finset (Cube d)) := by
    intro y _ z _ h
    simpa [neg_neg] using h
  have hsurj : Function.Surjective (fun y : Cube d => -y) := by
    intro y
    use -y
    simp
  rw [← Finset.sum_image hinj, Finset.image_univ_of_surjective hsurj]
end P2MHole01_de946156

/-! The sum over `Cube d = Fin d → ℤˣ` is invariant under pointwise negation,
an involution that permutes the cube. -/
lemma cube_sum_neg_inv {d : ℕ} (f : Cube d → ℝ) :
    (∑ y : Cube d, f (-y)) = ∑ y : Cube d, f y := by
  (first | exact P2MHole01_de946156.solution f | (apply P2MHole01_de946156.solution <;> assumption))

namespace P2MHole02_25ed77e0
theorem solution {d : ℕ} (S : Finset (Fin d)) (hOdd : Odd S.card) (y : Cube d) :
  parity S (-y) = -parity S y := by
  have hptw : ∀ j, sgn ((-y) j) = -sgn (y j) := by
    intro j
    simp [sgn, Int.cast_neg]
  rw [parity, parity]
  rw [Finset.prod_congr rfl (fun j _ => hptw j)]
  rw [Finset.prod_neg (fun j => sgn (y j))]
  obtain ⟨k, hk⟩ := hOdd
  rw [hk]
  simp [pow_add, pow_mul, pow_two, one_pow]
end P2MHole02_25ed77e0

/-! For `Odd S.card`, `parity S (-y) = - parity S y`. -/
lemma parity_neg_odd {d : ℕ} (S : Finset (Fin d)) (hOdd : Odd S.card) (y : Cube d) :
    parity S (-y) = - parity S y := by
  (first | exact P2MHole02_25ed77e0.solution S hOdd y | (apply P2MHole02_25ed77e0.solution <;> assumption))

namespace P2MHole03_21eab057
open Finset

/-- The complement `univ \ S`, as a named finset (usable at type position). -/
def solcompl {d : ℕ} (S : Finset (Fin d)) : Finset (Fin d) := Finset.univ \ S

/-- The equal-cardinality pieces we will glue: the complement of `S` has the
  same cardinality as the complement of `T`. -/
theorem solComplCard {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card) :
    (solcompl S).card = (solcompl T).card := by
  simp only [solcompl, Finset.card_sdiff, Finset.inter_univ]
  rw [h]

/-- A bijection `S ≃ T`, built from the canonical `s ≃ Fin s.card`. -/
noncomputable def solES {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card) : S ≃ T :=
  ((Finset.equivFin S).trans (finCongr h)).trans (Finset.equivFin T).symm

/-- A bijection `(univ \ S) ≃ (univ \ T)`. -/
noncomputable def solf {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card) :
    solcompl S ≃ solcompl T :=
  ((Finset.equivFin (solcompl S)).trans (finCongr (solComplCard S T h))).trans
    (Finset.equivFin (solcompl T)).symm

/-- Pack `x ∉ S` into the subtype `univ \ S`. -/
def solcs {d : ℕ} (S : Finset (Fin d)) (x : Fin d) (hx : x ∉ S) : solcompl S :=
  ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩

/-- Pack `y ∉ T` into the subtype `univ \ T`. -/
def solct {d : ℕ} (T : Finset (Fin d)) (y : Fin d) (hy : y ∉ T) : solcompl T :=
  ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩⟩

/-- The permutation: on `S` it acts as `solES`, on the complement as `solf`. -/
noncomputable def solπ {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card) : Fin d → Fin d :=
  fun x =>
    if hx : x ∈ S then (solES S T h ⟨x, hx⟩).val else (solf S T h (solcs S x hx)).val

/-- On a point of `S`, `solπ` is `solES`. -/
theorem solπ_of_mem {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card)
    (x : Fin d) (hx : x ∈ S) : (solπ S T h) x = (solES S T h ⟨x, hx⟩).val := by
  dsimp only [solπ]
  simp [hx]

/-- On a point outside `S`, `solπ` is `solf` of the complement point. -/
theorem solπ_of_notmem {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card)
    (x : Fin d) (hx : x ∉ S) : (solπ S T h) x = (solf S T h (solcs S x hx)).val := by
  dsimp only [solπ]
  simp [hx]

/-- The image side of `solES`/`solf`: values land in `T` / outside `T`. -/
theorem solES_inT {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card) (x : Fin d) (hx : x ∈ S) :
    (solES S T h ⟨x, hx⟩).val ∈ T := (solES S T h ⟨x, hx⟩).2

theorem solf_notinT {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card) (x : Fin d) (hx : x ∉ S) :
    (solf S T h (solcs S x hx)).val ∉ T :=
  Finset.mem_sdiff.mp (solf S T h (solcs S x hx)).2 |>.2

theorem solInj {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card) :
    Function.Injective (solπ S T h) := by
  intro a b hab
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · -- a, b ∈ S: both images live in T, and equal images force equal domain points
      have h1 : solES S T h ⟨a, ha⟩ = solES S T h ⟨b, hb⟩ := by
        have hπa : (solπ S T h) a = (solES S T h ⟨a, ha⟩).val := solπ_of_mem S T h a ha
        have hπb : (solπ S T h) b = (solES S T h ⟨b, hb⟩).val := solπ_of_mem S T h b hb
        have h2 : (solES S T h ⟨a, ha⟩).val = (solES S T h ⟨b, hb⟩).val := by
          rw [← hπa, hab, hπb]
        exact Subtype.coe_injective h2
      have h2 : (⟨a, ha⟩ : S) = (⟨b, hb⟩ : S) := by
        simpa [Equiv.symm_apply_apply] using congrArg ((solES S T h).symm) h1
      exact congrArg Subtype.val h2
    · -- a ∈ S, b ∉ S: the images lie in T and outside T
      have hπa : (solπ S T h) a = (solES S T h ⟨a, ha⟩).val := solπ_of_mem S T h a ha
      have hπb : (solπ S T h) b = (solf S T h (solcs S b hb)).val := solπ_of_notmem S T h b hb
      have hL : (solES S T h ⟨a, ha⟩).val ∈ T := solES_inT S T h a ha
      have hR : (solf S T h (solcs S b hb)).val ∉ T := solf_notinT S T h b hb
      have hbad : (solf S T h (solcs S b hb)).val ∈ T := by
        rw [← hπb, ← hab, hπa]
        exact hL
      exact (hR hbad).elim
  · by_cases hb : b ∈ S
    · -- a ∉ S, b ∈ S: symmetric to the previous mixed case
      have hπa : (solπ S T h) a = (solf S T h (solcs S a ha)).val := solπ_of_notmem S T h a ha
      have hπb : (solπ S T h) b = (solES S T h ⟨b, hb⟩).val := solπ_of_mem S T h b hb
      have hL : (solES S T h ⟨b, hb⟩).val ∈ T := solES_inT S T h b hb
      have hR : (solf S T h (solcs S a ha)).val ∉ T := solf_notinT S T h a ha
      have hbad : (solf S T h (solcs S a ha)).val ∈ T := by
        rw [← hπa, hab, hπb]
        exact hL
      exact (hR hbad).elim
    · -- a, b ∉ S: both images live outside T
      have hsub : solf S T h (solcs S a ha) = solf S T h (solcs S b hb) := by
        have hπa : (solπ S T h) a = (solf S T h (solcs S a ha)).val := solπ_of_notmem S T h a ha
        have hπb : (solπ S T h) b = (solf S T h (solcs S b hb)).val := solπ_of_notmem S T h b hb
        have h2 : (solf S T h (solcs S a ha)).val = (solf S T h (solcs S b hb)).val := by
          rw [← hπa, hab, hπb]
        exact Subtype.coe_injective h2
      have h2 : solcs S a ha = solcs S b hb := by
        simpa [Equiv.symm_apply_apply] using congrArg ((solf S T h).symm) hsub
      exact congrArg Subtype.val h2

theorem solSurj {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card) :
    Function.Surjective (solπ S T h) := by
  intro y
  by_cases hyT : y ∈ T
  · set z : S := (solES S T h).symm ⟨y, hyT⟩
    have hz : z.val ∈ S := z.2
    use z.val
    have hπz : (solπ S T h) z.val = (solES S T h ⟨z.val, hz⟩).val := solπ_of_mem S T h z.val hz
    rw [hπz]
    simp [z]
  · set w : solcompl S := (solf S T h).symm (solct T y hyT)
    have hw : w.val ∉ S := Finset.mem_sdiff.mp w.2 |>.2
    use w.val
    have hπw : (solπ S T h) w.val = (solf S T h (solcs S w.val hw)).val := solπ_of_notmem S T h w.val hw
    rw [hπw]
    simp [w, solct, solcs]

theorem solImage {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card) :
    Finset.image (⇑(Equiv.ofBijective (solπ S T h) ⟨solInj S T h, solSurj S T h⟩)) S = T := by
  change Finset.image (solπ S T h) S = T
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    -- x = ⇑(ofBijective …) y with y ∈ S; show x ∈ T
    rw [solπ_of_mem S T h y hy]
    exact (solES S T h ⟨y, hy⟩).2
  · intro hxT
    set z : S := (solES S T h).symm ⟨x, hxT⟩
    have hz : z.val ∈ S := z.2
    refine Finset.mem_image.mpr ⟨z.val, hz, ?_⟩
    have hπz : (solπ S T h) z.val = (solES S T h ⟨z.val, hz⟩).val := solπ_of_mem S T h z.val hz
    rw [hπz]
    simp [z]

theorem solution {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card) :
  ∃ (π : Equiv.Perm (Fin d)), Finset.image (⇑π) S = T := by
  refine ⟨Equiv.ofBijective (solπ S T h) ⟨solInj S T h, solSurj S T h⟩, ?_⟩
  exact solImage S T h
end P2MHole03_21eab057

/-- A permutation `π` with `π '' S = T` exists whenever `S.card = T.card`. -/
lemma exists_perm_between_finsets {d : ℕ} (S T : Finset (Fin d)) (h : S.card = T.card) :
    ∃ π : Equiv.Perm (Fin d), Finset.image π S = T := by
  (first | exact P2MHole03_21eab057.solution S T h | (apply P2MHole03_21eab057.solution <;> assumption))

namespace P2MHole04_b76a4150
theorem solution {d : ℕ} (f : Cube d → ℝ) (π : Equiv.Perm (Fin d)) :
  ∑ y : Cube d, f (y ∘ ⇑π) = ∑ y : Cube d, f y := by
  have h1 : (∑ y : Cube d, f (y ∘ ⇑π)) = ∑ y ∈ Finset.univ, f (y ∘ ⇑π) := rfl
  have h2 : (∑ y ∈ Finset.univ, f (y ∘ ⇑π)) = ∑ y ∈ Finset.univ, f y := by
    apply Finset.sum_bij
      (fun a _ => a ∘ ⇑π)
      (fun _ _ => Finset.mem_univ _)
      (fun a1 _ a2 _ heq => by
        ext j
        have h := congr_fun heq (π.symm j)
        rw [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply] at h
        rw [h])
      (fun z _ => by
        refine ⟨z ∘ π.symm, Finset.mem_univ _, ?_⟩
        ext j
        rw [Function.comp_apply, Function.comp_apply, Equiv.symm_apply_apply])
      (fun _ _ => rfl)
  rw [h1, h2]
end P2MHole04_b76a4150

/-! The sum over `Cube d` is invariant under composing with a coordinate permutation. -/
lemma cube_sum_perm_inv {d : ℕ} (f : Cube d → ℝ) (π : Equiv.Perm (Fin d)) :
    (∑ y : Cube d, f (y ∘ π)) = ∑ y : Cube d, f y := by
  (first | exact P2MHole04_b76a4150.solution f π | (apply P2MHole04_b76a4150.solution <;> assumption))

namespace P2MHole05_b0ecc4c8
theorem solution {d : ℕ} (S : Finset (Fin d)) (π : Equiv.Perm (Fin d)) (y : Cube d) :
  parity S (y ∘ ⇑π) = parity (Finset.image (⇑π) S) y := by
  simp only [parity]
  rw [show (∏ j ∈ S, sgn ((y ∘ ⇑π) j)) = ∏ j ∈ S, sgn (y (⇑π j)) from by simp only [Function.comp_apply]]
  rw [← Finset.prod_image (f := fun i : Fin d => sgn (y i)) (s := S) (g := ⇑π) (Set.injOn_of_injective π.injective)]
end P2MHole05_b0ecc4c8

-- riskiest
/-- Composing the argument with a permutation pushes the character's support forward:
`parity S (y ∘ π) = parity (π '' S) y`. (The earlier form `parity (π '' S) (y ∘ π) = parity S y`
was false.) -/
lemma parity_perm_push {d : ℕ} (S : Finset (Fin d)) (π : Equiv.Perm (Fin d)) (y : Cube d) :
    parity S (y ∘ π) = parity (Finset.image π S) y := by
  (first | exact P2MHole05_b0ecc4c8.solution S π y | (apply P2MHole05_b0ecc4c8.solution <;> assumption))

theorem solution (d : ℕ) (g : Cube d → ℝ) :
    ((∀ y, g (-y) = g y) → ∀ S : Finset (Fin d), Odd S.card → fourierCoeff g S = 0) ∧
    ((∀ (π : Equiv.Perm (Fin d)) (y : Cube d), g (y ∘ π) = g y) →
      ∀ S T : Finset (Fin d), S.card = T.card → fourierCoeff g S = fourierCoeff g T) := by
  constructor
  · intro hEven S hOdd
    unfold PriceCapacities.LowerBound.fourierCoeff PriceCapacities.LowerBound.cubeInner
    have hsum : (∑ y : Cube d, g y * parity S y) = 0 := by
      have h1 : (∑ y : Cube d, g y * parity S y) = ∑ y : Cube d, g (-y) * parity S (-y) :=
        (cube_sum_neg_inv (fun y => g y * parity S y)).symm
      have h2 : (∑ y : Cube d, g (-y) * parity S (-y)) = -(∑ y : Cube d, g y * parity S y) := by
        simp [hEven, parity_neg_odd S hOdd]
      rw [h1, h2]
      linarith
    rw [hsum]
    ring
  · intro hPerm S T hcard
    obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin d), Finset.image π S = T :=
      exists_perm_between_finsets S T hcard
    unfold PriceCapacities.LowerBound.fourierCoeff PriceCapacities.LowerBound.cubeInner
    have hsum : (∑ y : Cube d, g y * parity T y) = ∑ y : Cube d, g y * parity S y := by
      calc
        _ = ∑ y : Cube d, g y * parity S (y ∘ π) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← hπ, (parity_perm_push S π y).symm]
        _ = ∑ y : Cube d, g (y ∘ π) * parity S (y ∘ π) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [(hPerm π y).symm]
        _ = ∑ y : Cube d, g y * parity S y :=
          cube_sum_perm_inv (fun y => g y * parity S y) π
    rw [hsum]
