-- Prove2me | solution 1 for StrategicAlloc.EFXFour.vstar_efx_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:39:10.167452+00:00
-- url     : https://prove2.me/submissions/ea5ce787-a641-4f77-baba-824390c7383e

import Mathlib
import Definitions.Def_StrategicAlloc_EFXFour_Setting

set_option autoImplicit false
open StrategicAlloc.EFXFour

def vN : Fin 4 → ℕ := ![12, 10, 10, 1]

def PP (A : Fin 2 → Finset (Fin 4)) : Prop :=
  ∀ i j : Fin 2, (A j).Nonempty → ∀ g ∈ A j,
    ∑ x ∈ (A j).erase g, vN x ≤ ∑ x ∈ A i, vN x

instance : DecidablePred PP := fun A => by unfold PP; infer_instance

set_option maxRecDepth 100000 in
theorem hdec : ∀ S : Finset (Fin 4), PP ![S, Sᶜ] ↔ (S = {0, 3} ∨ S = {1, 2}) := by decide

theorem hval (S : Finset (Fin 4)) (i : Fin 2) :
    StrategicAlloc.RRFair.val (fun _ : Fin 2 => vstar) i S = ((∑ g ∈ S, vN g : ℕ) : ℝ) / 10 := by
  unfold StrategicAlloc.RRFair.val
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro g _
  fin_cases g <;> simp [vstar, vN] <;> norm_num

theorem hpos (i : Fin 2) (g : Fin 4) : 0 < (fun _ : Fin 2 => vstar) i g := by
  fin_cases g <;> simp [vstar] <;> norm_num

theorem solution (A : Fin 2 → Finset (Fin 4)) (hA : StrategicAlloc.RRFair.IsAllocation A) :
    StrategicAlloc.CutChoose.IsEFX (fun _ => vstar) A ↔ A = ![{0, 3}, {1, 2}] ∨ A = ![{1, 2}, {0, 3}] := by
  obtain ⟨hdisj, hcover⟩ := hA
  have hA1 : A 1 = (A 0)ᶜ := by
    ext x
    have hx : x ∈ Finset.univ.biUnion A := by rw [hcover]; exact Finset.mem_univ x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Fin.exists_fin_two] at hx
    have hd := Finset.disjoint_left.1 (hdisj (show (0 : Fin 2) ≠ 1 by decide))
    simp only [Finset.mem_compl]
    constructor
    · intro h h0
      exact hd h0 h
    · intro h
      rcases hx with h0 | h1
      · exact absurd h0 h
      · exact h1
  have hAeq : A = ![A 0, (A 0)ᶜ] := by
    funext i
    fin_cases i
    · simp
    · simpa using hA1
  have hiff : StrategicAlloc.CutChoose.IsEFX (fun _ => vstar) A ↔ PP A := by
    unfold StrategicAlloc.CutChoose.IsEFX PP
    constructor
    · intro h i j hne g hg
      have h' := h i j hne g hg (hpos i g)
      rw [hval, hval] at h'
      have := (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 10)).1 h'
      exact_mod_cast this
    · intro h i j hne g hg _
      rw [hval, hval]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast h i j hne g hg
  rw [hiff]
  have hP : PP A ↔ PP ![A 0, (A 0)ᶜ] := by rw [← hAeq]
  rw [hP, hdec (A 0)]
  have c1 : (({0, 3} : Finset (Fin 4))ᶜ) = {1, 2} := by decide
  have c2 : (({1, 2} : Finset (Fin 4))ᶜ) = {0, 3} := by decide
  constructor
  · rintro (h | h)
    · left
      funext i
      fin_cases i
      · simpa using h
      · simp [hA1, h, c1]
    · right
      funext i
      fin_cases i
      · simpa using h
      · simp [hA1, h, c2]
  · rintro (h | h)
    · left
      simpa using congrFun h 0
    · right
      simpa using congrFun h 0
