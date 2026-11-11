-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P78.reduced_resource_is_permutation
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T13:49:47.189137+00:00
-- url     : https://prove2.me/submissions/f23124f0-473d-4ae2-bd2a-ff18daee89e9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P78

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P78

attribute [local instance] Classical.propDecidable Classical.decEq

-- Swapping with the last label identifies Fin m with the complement of hat.
theorem p007_liftLabel_injective {m : ℕ} (hat : Fin (m + 1)) :
    Function.Injective (liftLabel hat) := by
  intro a b hab
  have h := (Equiv.swap hat (Fin.last m)).injective hab
  apply Fin.ext
  exact congrArg (fun z : Fin (m + 1) => z.val) h

theorem p007_liftLabel_ne {m : ℕ} (hat : Fin (m + 1)) (a : Fin m) :
    liftLabel hat a ≠ hat := by
  intro h
  have h' := congrArg (Equiv.swap hat (Fin.last m)) h
  have he : a.castSucc = Fin.last m := by simpa [liftLabel] using h'
  have hv := congrArg Fin.val he
  have ha := a.isLt
  change (a : ℕ) = m at hv
  omega

theorem p007_dropLabel_liftLabel {m : ℕ} (hm : 0 < m)
    (hat : Fin (m + 1)) (a : Fin m) :
    dropLabel hm hat (liftLabel hat a) = a := by
  apply Fin.ext
  simp [dropLabel, liftLabel, Nat.mod_eq_of_lt a.isLt]

theorem p007_liftLabel_dropLabel {m : ℕ} (hm : 0 < m)
    (hat v : Fin (m + 1)) (hv : v ≠ hat) :
    liftLabel hat (dropLabel hm hat v) = v := by
  have hne : Equiv.swap hat (Fin.last m) v ≠ Fin.last m := by
    intro h
    have h' := congrArg (Equiv.swap hat (Fin.last m)) h
    exact hv (by simpa using h')
  have hlt : (Equiv.swap hat (Fin.last m) v).val < m := by
    have hle := (Equiv.swap hat (Fin.last m) v).isLt
    have hval : (Equiv.swap hat (Fin.last m) v).val ≠ m := by
      intro h
      apply hne
      exact Fin.ext h
    omega
  have hcast : (dropLabel hm hat v).castSucc = Equiv.swap hat (Fin.last m) v := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hlt
  unfold liftLabel
  rw [hcast]
  simp

theorem p007_dropLabel_injective_on_complement {m : ℕ} (hm : 0 < m)
    (hat u v : Fin (m + 1)) (hu : u ≠ hat) (hv : v ≠ hat)
    (h : dropLabel hm hat u = dropLabel hm hat v) : u = v := by
  have h' := congrArg (liftLabel hat) h
  simpa only [p007_liftLabel_dropLabel hm hat u hu,
    p007_liftLabel_dropLabel hm hat v hv] using h'

-- The splice avoids the deleted output. If the original edge hits bhat,
-- its replacement is f ahat, and injectivity excludes f ahat = bhat.
theorem p007_splice_ne {m : ℕ} (f : Equiv.Perm (Fin (m + 1)))
    (ahat bhat : Fin (m + 1)) (a : Fin m) :
    (if f (liftLabel ahat a) = bhat then f ahat else f (liftLabel ahat a)) ≠ bhat := by
  by_cases h : f (liftLabel ahat a) = bhat
  · simp only [if_pos h]
    intro h'
    exact p007_liftLabel_ne ahat a (f.injective (h.trans h'.symm))
  · simpa only [if_neg h] using h

theorem p007_reducedMap_injective {m : ℕ} (hm : 0 < m)
    (f : Equiv.Perm (Fin (m + 1))) (ahat bhat : Fin (m + 1)) :
    Function.Injective (reducedMap hm f ahat bhat) := by
  intro a b hab
  have h := p007_dropLabel_injective_on_complement hm bhat _ _
    (p007_splice_ne f ahat bhat a) (p007_splice_ne f ahat bhat b) hab
  by_cases ha : f (liftLabel ahat a) = bhat
  · by_cases hb : f (liftLabel ahat b) = bhat
    · exact p007_liftLabel_injective ahat (f.injective (ha.trans hb.symm))
    · simp only [if_pos ha, if_neg hb] at h
      exact False.elim (p007_liftLabel_ne ahat b (f.injective h).symm)
  · by_cases hb : f (liftLabel ahat b) = bhat
    · simp only [if_neg ha, if_pos hb] at h
      exact False.elim (p007_liftLabel_ne ahat a (f.injective h))
    · simp only [if_neg ha, if_neg hb] at h
      exact p007_liftLabel_injective ahat (f.injective h)

end QAlgorithms.Papers.Independent.Intakethird100.P78

open QAlgorithms.Papers.Independent.Intakethird100.P78

/-- The corrected deleted-label construction is a permutation system.
The original statement excludes m = 1, and that hypothesis is retained. -/
theorem solution
    {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    {m : ℕ} (hm : 1 < m)
    (F : X → Y → Equiv.Perm (Fin (m + 1))) :
    IsPermutationSystem (reducedKernel (lt_trans Nat.zero_lt_one hm) F) := by
  refine ⟨hm, (fun xa yb => reducedMap (lt_trans Nat.zero_lt_one hm)
    (F xa.1 yb.1) xa.2 yb.2), ?_, rfl⟩
  intro xa yb
  have h := p007_reducedMap_injective (lt_trans Nat.zero_lt_one hm)
    (F xa.1 yb.1) xa.2 yb.2
  exact ⟨h, Finite.surjective_of_injective h⟩

#print axioms solution

end
