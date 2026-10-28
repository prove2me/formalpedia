-- Prove2me | solution 2 for StableSKC.Galois.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:40.701647+00:00
-- url     : https://prove2.me/submissions/064af499-6611-4d9f-b80b-4fd181c09a4f

import Mathlib
import Definitions.Def_StableSKC_Galois_Model
import Theorems.Thm_StableSKC_Galois_degree_count
import Theorems.Thm_StableSKC_Galois_scale_round_formula

-- carved verbatim out of submission 5a6c971f-af0e-4a22-bf3b-e77d11471b4c, lines 274-283

noncomputable section
set_option autoImplicit false
open StableSKC.Galois
open StableSKC

lemma card_field {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (pb : PowerBasis (ZMod 2) F) : Fintype.card F = 2 ^ pb.dim := by
  calc
    Fintype.card F = Fintype.card (Fin pb.dim →₀ ZMod 2) :=
      Fintype.card_congr pb.basis.repr.toEquiv
    _ = 2 ^ pb.dim := by simp

lemma card_units {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] (pb : PowerBasis (ZMod 2) F) :
    Fintype.card Fˣ = 2 ^ pb.dim - 1 := by
  rw [Fintype.card_units, card_field pb]

lemma count_inv_mul {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (y : F) (hy : y ≠ 0) (p : F → Prop) [DecidablePred p] :
    (Finset.univ.filter fun z : Fˣ => p ((↑z⁻¹ : F) * y)).card =
      (Finset.univ.filter fun r : F => r ≠ 0 ∧ p r).card := by
  classical
  apply Finset.card_bij (fun (z : Fˣ) _ => (↑z⁻¹ : F) * y)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨mul_ne_zero (Units.ne_zero _) hy, hz⟩
  · intro z hz w hw heq
    apply inv_injective
    apply Units.ext
    exact mul_right_cancel₀ hy heq
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    let z : Fˣ := Units.mk0 (y / r) (div_ne_zero hy hr.1)
    have hz : (↑z⁻¹ : F) * y = r := by
      simp [z, div_eq_mul_inv, mul_comm, hy]
    refine ⟨z, ?_, hz⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hz.symm ▸ hr.2

lemma meeting_count {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] (pb : PowerBasis (ZMod 2) F) (T : Seeding pb.dim F)
    (hT : ∀ x y : F, x ≠ y → CanMeetIn T x y (1 + deg pb (x - y)))
    (x x' : F) (hxx' : x ≠ x') (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ pb.dim) :
    meetCount (fun z : Fˣ => scale T z) x x' i = 2 ^ (i - 1) := by
  classical
  have hy : x - x' ≠ 0 := sub_ne_zero.mpr hxx'
  unfold meetCount
  calc
    (Finset.univ.filter fun z : Fˣ => CanMeetIn (scale T z) x x' i).card =
        (Finset.univ.filter fun z : Fˣ => 1 + deg pb ((↑z⁻¹ : F) * (x - x')) = i).card := by
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hround := scale_round_formula pb T hT z
      exact (hround.1 x x' hxx' i).trans ((hround.2 (x - x') hy i).trans eq_comm)
    _ = (Finset.univ.filter fun r : F => r ≠ 0 ∧ 1 + deg pb r = i).card :=
      count_inv_mul (x - x') hy (fun r => 1 + deg pb r = i)
    _ = 2 ^ (i - 1) := degree_count pb i hi1 hik

end

section
set_option autoImplicit false
open StableSKC.Galois

theorem solution {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    (pb : PowerBasis (ZMod 2) F) (T : Seeding pb.dim F)
    (hT : ∀ x y : F, x ≠ y → CanMeetIn T x y (1 + deg pb (x - y))) :
    IsStableSKC (fun z : Fˣ => scale T z) ∧
    ∀ x x' : F, x ≠ x' → ∀ i : ℕ, 1 ≤ i → i ≤ pb.dim →
      meetCount (fun z : Fˣ => scale T z) x x' i = 2 ^ (i - 1) := by
  refine ⟨⟨card_units pb, ?_⟩, meeting_count pb T hT⟩
  intro i hi1 hik
  exact ⟨2 ^ (i - 1), fun x x' hxx' => meeting_count pb T hT x x' hxx' i hi1 hik⟩

end
