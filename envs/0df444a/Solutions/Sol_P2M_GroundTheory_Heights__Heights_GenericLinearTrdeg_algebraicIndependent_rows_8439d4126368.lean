-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_algebraicIndependent_rows_8439d4126368
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:11.289811+00:00
-- url     : https://prove2.me/submissions/74f4deee-70d0-4b5b-abbe-7cf0c75d056c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PGenericLinearTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_algebraicIndependent_pair_linear_9149b1566c10
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_transcendental_of_subset_ee23a7243d92
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_adjoin_subset_797b8e5e09f9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.GenericLinearTrdeg
namespace GroundTheory.Heights₂.Heights.GenericLinearTrdeg
theorem _root_.solution (F E : Type) [Field F] [Field E] [Algebra F E] (N k r : ℕ)
    (η : Fin N → E) (hrk : r ≤ k) (j : Fin r → Fin N) (hind : AlgebraicIndependent F (η ∘ j)) :
    AlgebraicIndependent F (Sum.elim (fun ij : Fin k × Fin N => (X ij : MvPolynomial (Fin k × Fin N) E))
      (fun l : Fin r => ∑ m, X (Fin.castLE hrk l, m) * C (η m))) := by
  classical
  let sf : Fin k → MvPolynomial (Fin k × Fin N) E := fun i => ∑ m, X (i, m) * C (η m)
  let g : ℕ → (Fin k × Fin N) ⊕ Fin r → MvPolynomial (Fin k × Fin N) E := fun i =>
    Sum.elim X (fun l => if (l : ℕ) < i then sf (Fin.castLE hrk l) else C (η (j l)))
  have key : ∀ i ≤ r, AlgebraicIndependent F (g i) := by
    intro i
    induction i with
    | zero =>
      intro _
      have := AlgebraicIndependent.sumElim_comp (S := E) hind
        (MvPolynomial.algebraicIndependent_X (Fin k × Fin N) E)
      convert this using 1
      funext t
      rcases t with t | l
      · rfl
      · simp [g, MvPolynomial.algebraMap_eq]
    | succ i ih =>
      intro hi
      have IH := ih (by omega)
      let il : Fin r := ⟨i, by omega⟩
      let i' : Fin k := Fin.castLE hrk il
      let m0 : Fin N := j il
      have hgt : ∀ t, t ≠ Sum.inr il → g (i+1) t = g i t := by
        rintro (t | l) ht
        · rfl
        · have hl : (l : ℕ) ≠ i := fun h => ht (by rw [show l = il from Fin.ext h])
          simp only [g, Sum.elim_inr]
          rcases Nat.lt_or_ge l i with h | h
          · rw [if_pos h, if_pos (by omega)]
          · rw [if_neg (by omega), if_neg (by omega)]
      rw [AlgebraicIndependent.iff_transcendental_adjoin_image (Sum.inr il)]
      refine ⟨?_, ?_⟩
      · have h1 := ((AlgebraicIndependent.iff_transcendental_adjoin_image (Sum.inr il)).mp IH).1
        convert h1 using 1
        funext t
        exact hgt t.1 t.2
      · have himg : g (i+1) '' {Sum.inr il}ᶜ = g i '' {Sum.inr il}ᶜ :=
          Set.image_congr (fun t ht => hgt t ht)
        rw [himg]
        have hval : g (i+1) (Sum.inr il) = sf i' := by simp [g, il, i']
        rw [hval]
        let U : Set ((Fin k × Fin N) ⊕ Fin r) := {Sum.inr il, Sum.inl (i', m0)}ᶜ
        let B := Algebra.adjoin F (g i '' U)
        let x : MvPolynomial (Fin k × Fin N) E := X (i', m0)
        let η0 : MvPolynomial (Fin k × Fin N) E := C (η m0)
        let rr : MvPolynomial (Fin k × Fin N) E := ∑ m ∈ Finset.univ.erase m0, X (i', m) * C (η m)
        have hsplit : sf i' = x * η0 + rr := (Finset.add_sum_erase _ _ (Finset.mem_univ m0)).symm
        have hη : Transcendental B η0 := by
          have := IH.transcendental_adjoin (s := U) (i := Sum.inr il) (by simp [U])
          simpa [g, il] using this
        let T : Subalgebra E (MvPolynomial (Fin k × Fin N) E) :=
          Algebra.adjoin E (X '' {(i', m0)}ᶜ)
        have hXT : ∀ ab, ab ≠ (i', m0) → (X ab : MvPolynomial (Fin k × Fin N) E) ∈ T :=
          fun ab h => Algebra.subset_adjoin ⟨ab, h, rfl⟩
        have hCT : ∀ e : E, (C e : MvPolynomial (Fin k × Fin N) E) ∈ T := fun e => T.algebraMap_mem e
        have hBT : (B : Set (MvPolynomial (Fin k × Fin N) E)) ⊆ T := by
          apply adjoin_subset T.toSubring
          · intro c
            exact hCT (algebraMap F E c)
          · rintro _ ⟨t, ht, rfl⟩
            rcases t with ab | l
            · exact hXT ab (fun h => ht (by simp [h]))
            · have hl : l ≠ il := fun h => ht (by simp [h])
              simp only [g, Sum.elim_inr]
              split_ifs with hli
              · apply T.sum_mem
                intro m _
                apply T.mul_mem _ (hCT _)
                apply hXT
                intro h
                have := congrArg (fun p => (p.1 : ℕ)) h
                simp [i', il] at this
                omega
              · exact hCT _
        have hx : Transcendental (Algebra.adjoin B ({η0, rr} : Set _)) x := by
          refine transcendental_of_subset _ T ?_
            ((MvPolynomial.algebraicIndependent_X _ E).transcendental_adjoin
              (s := {(i', m0)}ᶜ) (i := (i', m0)) (by simp))
          apply adjoin_subset T.toSubring
          · intro c
            exact hBT c.2
          · intro z hz
            rcases hz with rfl | hz
            · exact hCT _
            · rw [Set.mem_singleton_iff] at hz
              subst hz
              apply T.sum_mem
              intro m hm
              exact T.mul_mem (hXT _ (by simpa using (Finset.ne_of_mem_erase hm))) (hCT _)
        have hOV := algebraicIndependent_pair_linear hη hx
        have htr := hOV.transcendental_adjoin (s := {0}) (i := 1) (by simp)
        have htr' : Transcendental (Algebra.adjoin B (![x, x * η0 + rr] '' {0})) (x * η0 + rr) := htr
        rw [hsplit]
        refine transcendental_of_subset _ _ ?_ htr'
        apply adjoin_subset (Algebra.adjoin B (![x, x * η0 + rr] '' {0})).toSubring
        · intro c
          exact (Algebra.adjoin B (![x, x * η0 + rr] '' {0})).algebraMap_mem
            (⟨algebraMap F _ c, B.algebraMap_mem c⟩ : B)
        · rintro _ ⟨t, ht, rfl⟩
          by_cases htx : t = Sum.inl (i', m0)
          · subst htx
            exact Algebra.subset_adjoin ⟨0, rfl, rfl⟩
          · have htU : t ∈ U := by
              simp only [U, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              exact ⟨ht, htx⟩
            exact (Algebra.adjoin B (![x, x * η0 + rr] '' {0})).algebraMap_mem
              (⟨g i t, Algebra.subset_adjoin ⟨t, htU, rfl⟩⟩ : B)
  have := key r le_rfl
  convert this using 1
  funext t
  rcases t with t | l
  · rfl
  · simp [g, sf, l.2]
end GroundTheory.Heights₂.Heights.GenericLinearTrdeg
