-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P22.multilinearMap_continuous_lift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:20:06.805614+00:00
-- url     : https://prove2.me/submissions/dfc7afe8-c246-4128-8980-323a81a4881c

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22
open QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

theorem g67f2_closed {K : Type u} [RCLike K]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]
    {Z : Type z} [NormedAddCommGroup Z] [NormedSpace K Z]
    (L : E →ₗ[K] Y) (j : Y →L[K] Z) (hj : Function.Injective j)
    (hc : Continuous (fun x => j (L x))) : Continuous L := by
  apply LinearMap.continuous_of_isClosed_graph
  have : (L.graph : Set (E × Y)) = {p | j p.2 = j (L p.1)} := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_setOf_eq]
    exact ⟨fun h => by rw [h], fun h => hj h⟩
  rw [this]
  exact isClosed_eq (j.continuous.comp continuous_snd) (hc.comp continuous_fst)

theorem g67f2_cont {K : Type u} [RCLike K]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]
    {Z : Type z} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    (eta : Y →L[K] Z) (hEta : Function.Injective eta) :
    ∀ (n : ℕ) (X : Fin n → Type v)
    [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace K (X i)]
    [∀ i, CompleteSpace (X i)] (f : MultilinearMap K X Y),
    Continuous (fun x => eta (f x)) → Continuous f := by
  intro n
  induction n with
  | zero =>
    intro X _ _ _ f _
    exact continuous_of_const fun x y => by rw [Subsingleton.elim x y]
  | succ n ih =>
    intro X _ _ _ f hc
    have hx0 : ∀ x0 : X 0, Continuous (f.curryLeft x0) := by
      intro x0
      apply ih (fun i => X i.succ) (f.curryLeft x0)
      have : Continuous (fun m : (∀ i : Fin n, X i.succ) => (Fin.cons x0 m : ∀ i, X i)) :=
        continuous_const.finCons continuous_id
      exact hc.comp this
    let T : X 0 →ₗ[K] ContinuousMultilinearMap K (fun i : Fin n => X i.succ) Y :=
      { toFun := fun x0 => ⟨f.curryLeft x0, hx0 x0⟩
        map_add' := by
          intro a b; ext m
          show f.curryLeft (a + b) m = f.curryLeft a m + f.curryLeft b m
          rw [map_add]; rfl
        map_smul' := by
          intro c a; ext m
          show f.curryLeft (c • a) m = c • f.curryLeft a m
          rw [map_smul]; rfl }
    let j := ContinuousLinearMap.compContinuousMultilinearMapL K (fun i : Fin n => X i.succ) Y Z eta
    have hj : Function.Injective j := by
      intro g h hgh
      ext m
      apply hEta
      have := congrArg (fun F => F m) hgh
      simpa [j, ContinuousLinearMap.compContinuousMultilinearMapL_apply] using this
    let A0 : ContinuousMultilinearMap K X Z :=
      { toMultilinearMap := (eta : Y →ₗ[K] Z).compMultilinearMap f, cont := hc }
    have hT : Continuous T := by
      apply g67f2_closed T j hj
      have : (fun x => j (T x)) = fun x => A0.curryLeft x := by
        funext x0; ext m
        rfl
      rw [this]
      exact A0.curryLeft.continuous
    let Tc : X 0 →L[K] ContinuousMultilinearMap K (fun i : Fin n => X i.succ) Y := ⟨T, hT⟩
    have : (f : (∀ i, X i) → Y) = fun m => Tc.uncurryLeft m := by
      funext m
      show f m = f (Fin.cons (m 0) (Fin.tail m))
      rw [Fin.cons_self_tail]
    rw [this]
    exact Tc.uncurryLeft.cont

/-- Lemma 9.1, PDF pp. 27–28. -/
theorem solution
    {K : Type u} [RCLike K]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Type v)
    [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace K (X i)]
    [∀ i, CompleteSpace (X i)]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]
    {Z : Type z} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    (eta : Y →L[K] Z) (hEta : Function.Injective eta)
    (A : ContinuousMultilinearMap K X Z)
    (hRange : ∀ x, ∃ y : Y, eta y = A x) :
    ∃! B : ContinuousMultilinearMap K X Y, ∀ x, eta (B x) = A x := by
  classical
  choose b hb using hRange
  let Bm : MultilinearMap K X Y :=
    { toFun := b
      map_update_add' := by
        intro _ m i x y
        apply hEta
        rw [map_add, hb, hb, hb]
        convert A.map_update_add m i x y
      map_update_smul' := by
        intro _ m i c x
        apply hEta
        rw [map_smul, hb, hb]
        convert A.map_update_smul m i c x }
  have hc : Continuous Bm := by
    apply g67f2_cont eta hEta n X Bm
    have : (fun x => eta (Bm x)) = fun x => A x := funext fun x => hb x
    rw [this]; exact A.cont
  refine ⟨⟨Bm, hc⟩, fun x => hb x, fun B' hB' => ?_⟩
  ext x
  apply hEta
  rw [hB' x]
  exact (hb x).symm
