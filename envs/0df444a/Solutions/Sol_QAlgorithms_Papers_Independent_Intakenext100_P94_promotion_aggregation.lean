-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P94.promotion_aggregation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:37:03.085207+00:00
-- url     : https://prove2.me/submissions/b949fcac-51ae-4e3d-aa44-6b9b748c7b15

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Intakenext100.P94 in
theorem solution :
    (∀ {m n k : ℕ} (chi : Fin m ↪ Fin n) (F : Tensor m k) u,
      promote chi F (fun a => chi (u a)) = F u) ∧
    (∀ {m n k : ℕ} (chi : Fin m ↪ Fin n) (s : Perm n) (p : Perm m) (F : Tensor m k),
      promote (relabelEmbedding chi s p) (permutationTensorAction p F) =
        permutationTensorAction s (promote chi F)) ∧
    (∀ {n k : ℕ} {C : Type*} [Fintype C] (s : Perm n) (F : C → Tensor n k),
      (∑ a, permutationTensorAction s (F a)) = permutationTensorAction s (∑ a, F a)) ∧
    (∀ {n k l : ℕ} (s : Perm n) (F : Tensor n k) (G : Tensor n l) t,
      tensorOuterProduct (permutationTensorAction s F) (permutationTensorAction s G) t =
        tensorOuterProduct F G (fun a => s.symm (t a))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m n k chi F u
    unfold promote
    rw [Finset.sum_eq_single u]
    · rw [if_pos rfl]
    · intro u' _ hne
      rw [if_neg]
      intro h
      exact hne (funext fun a => chi.injective (congrFun h a))
    · intro h
      exact absurd (Finset.mem_univ u) h
  · intro m n k chi s p F
    funext t
    show (∑ u : Fin k → Fin m, if (fun a => relabelEmbedding chi s p (u a)) = t then
        permutationTensorAction p F u else 0) =
      ∑ v : Fin k → Fin m, if (fun a => chi (v a)) = (fun a => s.symm (t a)) then F v else 0
    refine Fintype.sum_equiv (Equiv.piCongrRight (fun _ => p.symm)) _ _ (fun u => ?_)
    have hcond : ((fun a => relabelEmbedding chi s p (u a)) = t) ↔
        ((fun a => chi ((Equiv.piCongrRight (fun _ => p.symm) u) a)) =
          (fun a => s.symm (t a))) := by
      constructor
      · intro h
        funext a
        have := congrFun h a
        rw [← this]
        show chi (p.symm (u a)) = s.symm (s (chi (p.symm (u a))))
        rw [Equiv.symm_apply_apply]
      · intro h
        funext a
        have := congrFun h a
        show s (chi (p.symm (u a))) = t a
        have h2 : chi (p.symm (u a)) = s.symm (t a) := this
        rw [h2, Equiv.apply_symm_apply]
    by_cases hc : (fun a => relabelEmbedding chi s p (u a)) = t
    · rw [if_pos hc, if_pos (hcond.1 hc)]
      rfl
    · rw [if_neg hc, if_neg (fun h => hc (hcond.2 h))]
  · intro n k C _ s F
    exact (map_sum (permutationTensorAction s) F Finset.univ).symm
  · intro n k l s F G t
    rfl

end
