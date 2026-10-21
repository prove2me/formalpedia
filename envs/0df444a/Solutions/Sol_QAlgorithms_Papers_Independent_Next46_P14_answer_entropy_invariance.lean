-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P14.answer_entropy_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:21:29.906422+00:00
-- url     : https://prove2.me/submissions/32fce20a-fb49-45bc-9144-5bb34498645d

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14
noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Next46.P14

theorem g62g_ce_eq {O O' A B : Type*} (p : ℕ) (P : PMF O) (P' : PMF O')
    (X : O → A) (Y : O → B) (X' : O' → A) (Y' : O' → B)
    (h : P.map (fun x => (X x, Y x)) = P'.map (fun x => (X' x, Y' x))) :
    spirConditionalEntropy p P X Y = spirConditionalEntropy p P' X' Y' := by
  have hY : P.map Y = P'.map Y' := by
    have h2 := congrArg (fun Q : PMF (A × B) => Q.map Prod.snd) h
    simp only [PMF.map_comp] at h2
    exact h2
  unfold spirConditionalEntropy
  simp only [h, hY]

theorem g62g_map_eq {O V A B : Type*} (P : PMF O) (v v' : O → V)
    (hv : P.map v = P.map v') (g : V → A × B) :
    P.map (fun x => g (v x)) = P.map (fun x => g (v' x)) := by
  have := congrArg (fun Q : PMF V => Q.map g) hv
  simp only [PMF.map_comp] at this
  exact this

theorem solution {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L)
    (hprivate : Private b) (k k2 : Fin m.K) (n : Fin m.N) :
    (spirConditionalEntropy m.p (dataLaw b) (observedAnswer b k n)
      (fun x => (x.1 k, b.query k x.2.1 n)) =
    spirConditionalEntropy m.p (dataLaw b) (observedAnswer b k2 n)
      (fun x => (x.1 k, b.query k2 x.2.1 n))) ∧
    (spirConditionalEntropy m.p (dataLaw b) (observedAnswer b k n)
      (fun x => b.query k x.2.1 n) =
    spirConditionalEntropy m.p (dataLaw b) (observedAnswer b k2 n)
      (fun x => b.query k2 x.2.1 n)) := by
  have hv := hprivate.1 k k2 n
  constructor
  · apply g62g_ce_eq
    exact g62g_map_eq (dataLaw b) _ _ hv (fun v => (v.2.1, (v.2.2.1 k, v.1)))
  · apply g62g_ce_eq
    exact g62g_map_eq (dataLaw b) _ _ hv (fun v => (v.2.1, v.1))
