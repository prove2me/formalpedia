-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P96.centreFree_centralSection_unique
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T04:46:25.330966+00:00
-- url     : https://prove2.me/submissions/690161b6-5e08-4612-8bd2-58fddf2d20e3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P96

open scoped Manifold ContDiff

universe u v w z

open QAlgorithms.Papers.Independent.Intake100.P96 in
theorem solution {m h e : ℕ} {M : Type u} {H : Type v} {E : Type w}
    [TopologicalSpace M] [ChartedSpace (RealModel m) M]
    [TopologicalSpace H] [ChartedSpace (RealModel h) H]
    [TopologicalSpace E] [ChartedSpace (RealModel e) E]
    [Group H]
    (B : LeftPrincipalBundle m h e M H E) (R : RightPrincipalStructure B)
    (centreFree : ∀ k : H, (∀ l : H, k * l = l * k) → k = 1) :
    ∀ s t : M → E, IsCentralSection B R s → IsCentralSection B R t →
      s = t := by
  intro s t hs ht
  funext x
  obtain ⟨k, hk, -⟩ := R.fibreTorsor (s x) (t x) (by rw [hs.2.1 x, ht.2.1 x])
  have htk : t x = B.leftAction k (s x) := by rw [← hk, hs.2.2 k x]
  have hcomm : ∀ l, k * l = l * k := by
    intro l
    have e1 : B.leftAction (l * k) (s x) = B.leftAction (k * l) (s x) := by
      rw [B.mulAction, B.mulAction, ← htk, ht.2.2 l x, htk, R.commute k l (s x), ← hs.2.2 l x]
    obtain ⟨g, -, hg⟩ := B.fibreTorsor (s x) (B.leftAction (k * l) (s x))
      (B.projectionLeft _ _).symm
    rw [hg (l * k) e1, hg (k * l) rfl]
  have hk1 : k = 1 := centreFree k hcomm
  rw [htk, hk1, B.oneAction]
