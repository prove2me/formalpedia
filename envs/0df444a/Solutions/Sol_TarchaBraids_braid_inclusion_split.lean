-- Prove2me | solution 1 for TarchaBraids.braid_inclusion_split
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-21T21:06:07.312033+00:00
-- url     : https://prove2.me/submissions/97a9dbfb-8c02-49a1-9615-c6a1dfa7e7a7

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

namespace SplitSol

/-- The far-commutation relation, read off inside the presented group. -/
theorem rel_comm {n : ℕ} (i j : Fin (n - 1)) (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    (sigma i : ArtinBraidGroup n) * sigma j = sigma j * sigma i := by
  have hr : (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹)
      ∈ braidRels n := Or.inl ⟨i, j, hij, rfl⟩
  have h1 := PresentedGroup.one_of_mem (rels := braidRels n) hr
  simp only [map_mul, map_inv] at h1
  have h2 : (sigma i : ArtinBraidGroup n) * sigma j * (sigma i)⁻¹ * (sigma j)⁻¹ = 1 := h1
  calc (sigma i : ArtinBraidGroup n) * sigma j
      = (sigma i * sigma j * (sigma i)⁻¹ * (sigma j)⁻¹) * (sigma j * sigma i) := by group
    _ = 1 * (sigma j * sigma i) := by rw [h2]
    _ = sigma j * sigma i := one_mul _

/-- The braid relation, read off inside the presented group. -/
theorem rel_braid {n : ℕ} (i j : Fin (n - 1)) (hij : (j : ℕ) = (i : ℕ) + 1) :
    (sigma i : ArtinBraidGroup n) * sigma j * sigma i = sigma j * sigma i * sigma j := by
  have hr : (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
      (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹) ∈ braidRels n :=
    Or.inr ⟨i, j, hij, rfl⟩
  have h1 := PresentedGroup.one_of_mem (rels := braidRels n) hr
  simp only [map_mul, map_inv] at h1
  have h2 : (sigma i : ArtinBraidGroup n) * sigma j * sigma i *
      (sigma j * sigma i * sigma j)⁻¹ = 1 := h1
  calc (sigma i : ArtinBraidGroup n) * sigma j * sigma i
      = (sigma i * sigma j * sigma i * (sigma j * sigma i * sigma j)⁻¹) *
          (sigma j * sigma i * sigma j) := by group
    _ = 1 * (sigma j * sigma i * sigma j) := by rw [h2]
    _ = sigma j * sigma i * sigma j := one_mul _

/-- The two Artin generators of `B₃`, sent to adjacent transpositions of `Fin 3`. -/
def permOf : Fin (3 - 1) → Equiv.Perm (Fin 3) := ![Equiv.swap 0 1, Equiv.swap 1 2]

theorem permRel : ∀ r ∈ braidRels 3, FreeGroup.lift permOf r = 1 := by
  intro r hr
  rcases hr with ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩
  · exfalso
    have h1 := i.isLt
    have h2 := j.isLt
    have h3 : ((i : ℤ) - (j : ℤ)).natAbs ≤ 1 := by omega
    omega
  · have hi : (i : ℕ) = 0 := by have := i.isLt; have := j.isLt; omega
    have hj : (j : ℕ) = 1 := by omega
    have ei : i = 0 := Fin.ext hi
    have ej : j = 1 := Fin.ext hj
    subst ei; subst ej
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    decide

/-- The two generators of `B₃` are distinct. -/
theorem sigma_zero_ne_one : (sigma (0 : Fin (3 - 1)) : ArtinBraidGroup 3) ≠ sigma 1 := by
  intro hEq
  have h := congrArg (PresentedGroup.toGroup permRel) hEq
  rw [show (sigma (0 : Fin (3-1)) : ArtinBraidGroup 3) = PresentedGroup.of 0 from rfl,
    show (sigma (1 : Fin (3-1)) : ArtinBraidGroup 3) = PresentedGroup.of 1 from rfl,
    PresentedGroup.toGroup.of, PresentedGroup.toGroup.of] at h
  have h2 := congrArg (fun e : Equiv.Perm (Fin 3) => e 0) h
  simp only [permOf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h2
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at h2
  exact absurd h2 (by decide)

end SplitSol

open SplitSol

theorem _root_.solution : ¬ ∀ (m n : ℕ) (h : m ≤ n),
    ∃ f : ArtinBraidGroup m →* ArtinBraidGroup n,
      (∀ i : Fin (m - 1), f (sigma i) = sigma (Fin.castLE (Nat.sub_le_sub_right h 1) i)) ∧
      ∃ g : ArtinBraidGroup n →* ArtinBraidGroup m, ∀ x, g (f x) = x := by
  intro H
  obtain ⟨f, hf, g, hg⟩ := H 3 5 (by norm_num)
  have e0 : ∀ hh : 3 - 1 ≤ 5 - 1, Fin.castLE hh (0 : Fin (3 - 1)) = (0 : Fin (5 - 1)) :=
    fun hh => Fin.ext (by simp)
  have e1 : ∀ hh : 3 - 1 ≤ 5 - 1, Fin.castLE hh (1 : Fin (3 - 1)) = (1 : Fin (5 - 1)) :=
    fun hh => Fin.ext (by simp)
  have hga : g (sigma (0 : Fin (5 - 1))) = sigma (0 : Fin (3 - 1)) := by
    have h0 := hg (sigma (0 : Fin (3 - 1)))
    rw [hf 0, e0] at h0
    exact h0
  have hgb : g (sigma (1 : Fin (5 - 1))) = sigma (1 : Fin (3 - 1)) := by
    have h0 := hg (sigma (1 : Fin (3 - 1)))
    rw [hf 1, e1] at h0
    exact h0
  -- transport the five-strand relations down to three strands
  have haz : sigma (0 : Fin (3-1)) * g (sigma (3 : Fin (5-1)))
      = g (sigma (3 : Fin (5-1))) * sigma (0 : Fin (3-1)) := by
    have hr := congrArg g (rel_comm (n := 5) 0 3 (by decide))
    rw [map_mul, map_mul, hga] at hr
    exact hr
  have hbz : sigma (1 : Fin (3-1)) * g (sigma (3 : Fin (5-1)))
      = g (sigma (3 : Fin (5-1))) * sigma (1 : Fin (3-1)) := by
    have hr := congrArg g (rel_comm (n := 5) 1 3 (by decide))
    rw [map_mul, map_mul, hgb] at hr
    exact hr
  have hby : sigma (1 : Fin (3-1)) * g (sigma (2 : Fin (5-1))) * sigma (1 : Fin (3-1))
      = g (sigma (2 : Fin (5-1))) * sigma (1 : Fin (3-1)) * g (sigma (2 : Fin (5-1))) := by
    have hr := congrArg g (rel_braid (n := 5) 1 2 (by decide))
    rw [map_mul, map_mul, map_mul, map_mul, hgb] at hr
    exact hr
  have hyz := congrArg g (rel_braid (n := 5) 2 3 (by decide))
  rw [map_mul, map_mul, map_mul, map_mul] at hyz
  -- `z` is central, because it commutes with both generators
  have hzall : ∀ w : ArtinBraidGroup 3, w * g (sigma (3 : Fin (5-1)))
      = g (sigma (3 : Fin (5-1))) * w := by
    intro w
    have hsig : Set.range (fun i : Fin (3-1) => (sigma i : ArtinBraidGroup 3))
        = Set.range (PresentedGroup.of (rels := braidRels 3)) := rfl
    have htop : Subgroup.closure
        (Set.range (fun i : Fin (3-1) => (sigma i : ArtinBraidGroup 3))) = ⊤ :=
      (congrArg Subgroup.closure hsig).trans (PresentedGroup.closure_range_of (braidRels 3))
    have hle : Subgroup.closure
        (Set.range (fun i : Fin (3-1) => (sigma i : ArtinBraidGroup 3)))
        ≤ Subgroup.centralizer ({g (sigma (3 : Fin (5-1)))} : Set (ArtinBraidGroup 3)) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨i, rfl⟩
      simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff]
      rintro v rfl
      fin_cases i
      · exact haz.symm
      · exact hbz.symm
    rw [htop] at hle
    exact ((Subgroup.mem_centralizer_iff.mp (hle trivial)) _ rfl).symm
  -- hence `y = z`
  have hyeqz : g (sigma (2 : Fin (5-1))) = g (sigma (3 : Fin (5-1))) := by
    have hc := hzall (g (sigma (2 : Fin (5-1))))
    have h1 : g (sigma (2 : Fin (5-1))) * (g (sigma (2 : Fin (5-1))) * g (sigma (3 : Fin (5-1))))
        = g (sigma (2 : Fin (5-1))) * (g (sigma (3 : Fin (5-1))) * g (sigma (3 : Fin (5-1)))) := by
      calc g (sigma (2 : Fin (5-1))) * (g (sigma (2 : Fin (5-1))) * g (sigma (3 : Fin (5-1))))
          = g (sigma (2 : Fin (5-1))) * (g (sigma (3 : Fin (5-1))) * g (sigma (2 : Fin (5-1)))) := by
            rw [hc]
        _ = g (sigma (2 : Fin (5-1))) * g (sigma (3 : Fin (5-1))) * g (sigma (2 : Fin (5-1))) :=
            (mul_assoc _ _ _).symm
        _ = g (sigma (3 : Fin (5-1))) * g (sigma (2 : Fin (5-1))) * g (sigma (3 : Fin (5-1))) := hyz
        _ = g (sigma (2 : Fin (5-1))) * g (sigma (3 : Fin (5-1))) * g (sigma (3 : Fin (5-1))) := by
            rw [← hc]
        _ = g (sigma (2 : Fin (5-1))) * (g (sigma (3 : Fin (5-1))) * g (sigma (3 : Fin (5-1)))) :=
            mul_assoc _ _ _
    exact mul_right_cancel (mul_left_cancel h1)
  -- hence `b = y`
  have hyb : sigma (1 : Fin (3-1)) * g (sigma (2 : Fin (5-1)))
      = g (sigma (2 : Fin (5-1))) * sigma (1 : Fin (3-1)) := by
    rw [hyeqz]; exact hzall _
  have hbeqy : sigma (1 : Fin (3-1)) = g (sigma (2 : Fin (5-1))) := by
    have h1 : sigma (1 : Fin (3-1)) * (sigma (1 : Fin (3-1)) * g (sigma (2 : Fin (5-1))))
        = sigma (1 : Fin (3-1)) * (g (sigma (2 : Fin (5-1))) * g (sigma (2 : Fin (5-1)))) := by
      calc sigma (1 : Fin (3-1)) * (sigma (1 : Fin (3-1)) * g (sigma (2 : Fin (5-1))))
          = sigma (1 : Fin (3-1)) * (g (sigma (2 : Fin (5-1))) * sigma (1 : Fin (3-1))) := by
            rw [hyb]
        _ = sigma (1 : Fin (3-1)) * g (sigma (2 : Fin (5-1))) * sigma (1 : Fin (3-1)) :=
            (mul_assoc _ _ _).symm
        _ = g (sigma (2 : Fin (5-1))) * sigma (1 : Fin (3-1)) * g (sigma (2 : Fin (5-1))) := hby
        _ = g (sigma (2 : Fin (5-1))) * (sigma (1 : Fin (3-1)) * g (sigma (2 : Fin (5-1)))) :=
            mul_assoc _ _ _
        _ = g (sigma (2 : Fin (5-1))) * (g (sigma (2 : Fin (5-1))) * sigma (1 : Fin (3-1))) := by
            rw [hyb]
        _ = sigma (1 : Fin (3-1)) * (g (sigma (2 : Fin (5-1))) * g (sigma (2 : Fin (5-1)))) := by
            have hc2 : Commute (sigma (1 : Fin (3-1)) : ArtinBraidGroup 3)
                (g (sigma (2 : Fin (5-1)))) := hyb
            rw [← mul_assoc]
            exact (hc2.mul_right hc2).symm
    exact mul_right_cancel (mul_left_cancel h1)
  -- so the two generators of B₃ commute, and the braid relation collapses
  have hab : sigma (0 : Fin (3-1)) * sigma (1 : Fin (3-1))
      = sigma (1 : Fin (3-1)) * sigma (0 : Fin (3-1)) := by
    rw [hbeqy, hyeqz]; exact hzall _
  have hcab : Commute (sigma (0 : Fin (3-1)) : ArtinBraidGroup 3) (sigma 1) := hab
  have habraid := rel_braid (n := 3) (0 : Fin (3-1)) 1 (by decide)
  have haeqb : (sigma (0 : Fin (3-1)) : ArtinBraidGroup 3) = sigma 1 := by
    have h1 : (sigma (0 : Fin (3-1)) : ArtinBraidGroup 3) * (sigma 0 * sigma 1)
        = sigma 0 * (sigma 1 * sigma 1) := by
      calc (sigma (0 : Fin (3-1)) : ArtinBraidGroup 3) * (sigma 0 * sigma 1)
          = sigma 0 * (sigma 1 * sigma 0) := by rw [hab]
        _ = sigma 0 * sigma 1 * sigma 0 := (mul_assoc _ _ _).symm
        _ = sigma 1 * sigma 0 * sigma 1 := habraid
        _ = sigma 1 * (sigma 0 * sigma 1) := mul_assoc _ _ _
        _ = sigma 1 * (sigma 1 * sigma 0) := by rw [hab]
        _ = sigma 1 * sigma 1 * sigma 0 := (mul_assoc _ _ _).symm
        _ = sigma 0 * (sigma 1 * sigma 1) := (hcab.mul_right hcab).symm
    exact mul_right_cancel (mul_left_cancel h1)
  exact sigma_zero_ne_one haeqb


#print axioms solution
