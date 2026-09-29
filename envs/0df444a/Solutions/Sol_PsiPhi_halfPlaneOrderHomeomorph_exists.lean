-- Prove2me | solution 1 for PsiPhi.halfPlaneOrderHomeomorph_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T19:32:13.905438+00:00
-- url     : https://prove2.me/submissions/c16e3773-513f-4950-bae5-de90a5a3c748

import Mathlib
import Definitions.Def_PsiPhi

namespace PsiPhi

noncomputable section

open Set

theorem phi_lt (n : ℕ) (y : ℝ) : phi n y < (n : ℝ) + 1 := by
  by_cases h : y ≤ (n : ℝ)
  · simp [phi, h]; linarith
  · have hpos : (0:ℝ) < 1 + y - n := by linarith
    rw [show phi n y = n + (y - n) / (1 + y - n) from by simp [phi, h],
        add_lt_add_iff_left _, div_lt_iff₀ hpos]
    linarith

theorem phi_psi (n : ℕ) (x : {x : ℝ // x < (n : ℝ) + 1}) :
    phi n (psi n x.1) = x.1 := by
  by_cases h : x.1 ≤ (n : ℝ)
  · rw [psi, if_pos h, phi, if_pos h]
  · have hd : (0:ℝ) < (n : ℝ) + 1 - x.1 := by linarith [x.2]
    have hpos : (0:ℝ) < (x.1 - n) / ((n : ℝ) + 1 - x.1) := div_pos (by linarith) hd
    rw [psi, if_neg h, phi, if_neg (not_le.mpr (by linarith))]
    field_simp; ring

theorem psi_phi (n : ℕ) (y : ℝ) : psi n (phi n y) = y := by
  by_cases h : y ≤ (n : ℝ)
  · rw [phi, if_pos h, psi, if_pos h]
  · have hpos : (0:ℝ) < 1 + y - n := by linarith
    have hpos2 : (0:ℝ) < (y - n) / (1 + y - n) := div_pos (by linarith) hpos
    rw [phi, if_neg h, psi, if_neg (not_le.mpr (by linarith))]
    field_simp; ring

def psiSub (n : ℕ) : {x : ℝ // x < (n : ℝ) + 1} → ℝ := fun x => psi n x.1

def phiSub (n : ℕ) (y : ℝ) : {x : ℝ // x < (n : ℝ) + 1} := ⟨phi n y, phi_lt n y⟩

def psiR (n : ℕ) (x : ℝ) : ℝ := (n : ℝ) + (x - n) / ((n : ℝ) + 1 - x)

def phiR (n : ℕ) (y : ℝ) : ℝ := (n : ℝ) + (y - n) / (1 + y - n)

theorem continuousOn_psiR (n : ℕ) :
    ContinuousOn (psiR n) (Ico ((n : ℝ)) ((n : ℝ) + 1)) := by
  have hnum := (continuousOn_id.sub continuousOn_const : ContinuousOn (fun x : ℝ => x - n) (Ico (n:ℝ) (n+1)))
  have hden := (continuousOn_const.sub continuousOn_id : ContinuousOn (fun x : ℝ => n + 1 - x) (Ico (n:ℝ) (n+1)))
  refine continuousOn_const.add (hnum.div hden ?_)
  intro x hx
  rcases Set.mem_Ico.mp hx with ⟨hx1, hx2⟩
  exact ne_of_gt (by linarith [hx1, hx2])

theorem frontier_Iic_eq (n : ℕ) : frontier {x : ℝ | x ≤ (n : ℝ)} = {(n : ℝ)} :=
  frontier_Iic' ⟨(n : ℝ) + 1, Set.mem_Ioi.mpr (by linarith)⟩

theorem continuousOn_psi (n : ℕ) : ContinuousOn (psi n) (Iio ((n : ℝ) + 1)) := by
  classical
  have heq : (psi n) = (fun x : ℝ => if x ≤ (n:ℝ) then x else psiR n x) :=
    funext fun x => by simp [psi, psiR]
  rw [heq]
  refine ContinuousOn.if (s := Iio ((n : ℝ) + 1)) (p := fun x : ℝ => x ≤ (n : ℝ))
    (f := fun x : ℝ => x) (g := psiR n) ?_ ?_ ?_
  · rintro a ⟨-, ha⟩
    rw [frontier_Iic_eq n, mem_singleton_iff] at ha
    subst ha
    simp [psiR]
  · exact continuousOn_id
  · rw [show Iio ((n : ℝ) + 1) ∩ closure {x : ℝ | ¬ (x ≤ (n : ℝ))}
        = Ico ((n : ℝ)) ((n : ℝ) + 1) by
      rw [show ({x : ℝ | ¬ (x ≤ (n : ℝ))} : Set ℝ) = Ioi ((n : ℝ)) by
            ext x; simp only [Set.mem_setOf_eq, Set.mem_Ioi, not_le],
          closure_Ioi' ⟨(n : ℝ) + 1, Set.mem_Ioi.mpr (by linarith)⟩]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_Ico]
      constructor <;> intro h <;> exact ⟨h.2, h.1⟩]
    exact continuousOn_psiR n

theorem continuous_phi (n : ℕ) : Continuous (phi n) := by
  classical
  have hright : ContinuousOn (phiR n) (Ici ((n : ℝ))) := by
    have hnum' : ContinuousOn (fun y : ℝ => y - (n : ℝ)) (Ici ((n : ℝ))) :=
      (continuous_id.sub continuous_const).continuousOn
    have hden' : ContinuousOn (fun y : ℝ => (1:ℝ) + y - (n : ℝ)) (Ici ((n : ℝ))) :=
      ((continuous_const.add continuous_id).sub continuous_const).continuousOn
    have hdiv : ContinuousOn (fun y : ℝ => (y - (n : ℝ)) / ((1:ℝ) + y - (n : ℝ)))
        (Ici ((n : ℝ))) := hnum'.div hden' fun _ hy =>
      ne_of_gt (by have hy' := (Set.mem_Ici.mp hy); linarith)
    exact continuousOn_const.add hdiv
  have heq : (phi n) = (fun y : ℝ => if y ≤ (n:ℝ) then y else phiR n y) :=
    funext fun y => by simp [phi, phiR]
  rw [heq]
  refine continuous_if (p := fun y : ℝ => y ≤ (n : ℝ))
    (f := fun y : ℝ => y) (g := phiR n) ?_ ?_ ?_
  · rintro a ha
    rw [frontier_Iic_eq n, mem_singleton_iff] at ha
    subst ha
    simp [phiR]
  · exact continuousOn_id
  · rw [show ({y : ℝ | ¬ (y ≤ (n : ℝ))} : Set ℝ) = Ioi ((n : ℝ)) by
          ext y; simp only [Set.mem_setOf_eq, Set.mem_Ioi, not_le],
        closure_Ioi' ⟨(n : ℝ) + 1, Set.mem_Ioi.mpr (by linarith)⟩]
    exact hright

def psiHomeomorph (n : ℕ) : {x : ℝ // x < (n : ℝ) + 1} ≃ₜ ℝ where
  toFun := psiSub n
  invFun := phiSub n
  left_inv x := Subtype.ext (phi_psi n x)
  right_inv y := psi_phi n y
  continuous_toFun := (continuousOn_psi n).domRestrict
  continuous_invFun := (continuous_phi n).subtype_mk fun y => phi_lt n y

end

end PsiPhi

open PsiPhi

/-- The half-line `{x // x < n + 1}` is homeomorphic to all of `ℝ`. -/
theorem solution (n : ℕ) :
    Nonempty ({x : ℝ // x < (n : ℝ) + 1} ≃ₜ ℝ) :=
  ⟨psiHomeomorph n⟩
