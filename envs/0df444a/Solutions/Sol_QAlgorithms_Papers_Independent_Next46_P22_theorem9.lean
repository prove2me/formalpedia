-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P22.theorem9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:39:59.679774+00:00
-- url     : https://prove2.me/submissions/0f9c5a56-1382-46be-9f04-dfc2569a1960

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

open QAlgorithms.Papers.Independent.Next46.P22
open Classical

namespace G61T

variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]

theorem homog_single (D : Grading F G V) (g : G) (v : V) (hv : Homogeneous D g v) :
    D.decomp v = Finsupp.single g v := by
  ext h
  rw [Finsupp.single_apply]
  split_ifs with hgh
  · subst hgh; exact hv
  · have := D.offDiagonal v g h (Ne.symm hgh)
    rw [hv] at this; exact this

theorem comp_homog (D : Grading F G V) (v : V) (g : G) : Homogeneous D g (D.decomp v g) :=
  D.diagonal v g

theorem decomp_homog_apply (D : Grading F G V) (g k : G) (v : V) (hv : Homogeneous D g v) :
    D.decomp v k = if g = k then v else 0 := by
  rw [homog_single D g v hv, Finsupp.single_apply]

/-- the graded average of p -/
noncomputable def avgL (E : Grading F G V) (p : V →ₗ[F] V) : V →ₗ[F] V :=
  Finsupp.lsum F (fun g => Finsupp.lapply g ∘ₗ E.decomp ∘ₗ p) ∘ₗ E.decomp

theorem avgL_apply (E : Grading F G V) (p : V →ₗ[F] V) (v : V) :
    avgL E p v = (E.decomp v).sum (fun g x => E.decomp (p x) g) := by
  simp [avgL]; rfl

theorem avgL_homog (E : Grading F G V) (p : V →ₗ[F] V) (g : G) (v : V) (hv : Homogeneous E g v) :
    avgL E p v = E.decomp (p v) g := by
  rw [avgL_apply, homog_single E g v hv, Finsupp.sum_single_index (by simp)]

theorem sum_homog_decomp (E : Grading F G V) (y : G →₀ V) (hy : ∀ g, Homogeneous E g (y g)) (k : G) :
    E.decomp (y.sum (fun _ x => x)) k = y k := by
  rw [Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single k]
  · rw [decomp_homog_apply E k k _ (hy k), if_pos rfl]
  · intro g _ hg; rw [decomp_homog_apply E g k _ (hy g), if_neg hg]
  · intro hk; rw [Finsupp.notMem_support_iff.mp hk, map_zero, Finsupp.zero_apply]

theorem decomp_avgL (E : Grading F G V) (p : V →ₗ[F] V) (x : V) (k : G) :
    E.decomp (avgL E p x) k = avgL E p (E.decomp x k) := by
  rw [avgL_homog E p k _ (comp_homog E x k), avgL_apply, Finsupp.sum, map_sum,
    Finsupp.finsetSum_apply, Finset.sum_eq_single k]
  · rw [decomp_homog_apply E k k _ (comp_homog E _ k), if_pos rfl]
  · intro g _ hg; rw [decomp_homog_apply E g k _ (comp_homog E _ g), if_neg hg]
  · intro hk; rw [Finsupp.notMem_support_iff.mp hk]; simp

theorem avgL_mem (E : Grading F G V) (p : V →ₗ[F] V) (W : Submodule F V) (hW : GradedSubspace E W)
    (hp : ∀ v, p v ∈ W) (v : V) : avgL E p v ∈ W := by
  rw [avgL_apply]
  exact Submodule.sum_mem _ (fun g _ => hW _ (hp _) g)

theorem avgL_id (E : Grading F G V) (p : V →ₗ[F] V) (W : Submodule F V) (hW : GradedSubspace E W)
    (hp : ∀ w ∈ W, p w = w) (w : V) (hw : w ∈ W) : avgL E p w = w := by
  rw [avgL_apply]
  conv_rhs => rw [← E.total w]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  dsimp only
  rw [hp _ (hW w hw g), E.diagonal]

variable {L : Type*} [LieRing L] [LieAlgebra F L] [LieRingModule L V] [LieModule F L V]

theorem avgL_lie (D : Grading F G L) (E : Grading F G V) (hE : GradedCompatible D E)
    (p : V →ₗ[F] V) (hp : ∀ (a : L) v, p ⁅a, v⁆ = ⁅a, p v⁆) (a : L) (v : V) :
    avgL E p ⁅a, v⁆ = ⁅a, avgL E p v⁆ := by
  have step1 : ∀ h g (a : L) (v : V), Homogeneous D h a → Homogeneous E g v →
      avgL E p ⁅a, v⁆ = ⁅a, avgL E p v⁆ := by
    intro h g a v ha hv
    rw [avgL_homog E p (h * g) _ (hE h g a v ha hv), avgL_homog E p g v hv, hp]
    conv_lhs => rw [← E.total (p v)]
    rw [Finsupp.sum, lie_sum, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single g]
    · rw [decomp_homog_apply E (h * g) (h * g) _ (hE h g a _ ha (comp_homog E _ g)), if_pos rfl]
    · intro k _ hk
      rw [decomp_homog_apply E (h * k) (h * g) _ (hE h k a _ ha (comp_homog E _ k)), if_neg]
      intro hc; exact hk (mul_left_cancel hc)
    · intro hk; rw [Finsupp.notMem_support_iff.mp hk]; simp
  have step2 : ∀ h (a : L) (v : V), Homogeneous D h a → avgL E p ⁅a, v⁆ = ⁅a, avgL E p v⁆ := by
    intro h a v ha
    rw [← E.total v, Finsupp.sum, lie_sum, map_sum, map_sum, lie_sum]
    exact Finset.sum_congr rfl (fun g _ => step1 h g a _ ha (comp_homog E v g))
  rw [← D.total a, Finsupp.sum, sum_lie, map_sum, sum_lie]
  exact Finset.sum_congr rfl (fun h _ => step2 h _ v (comp_homog D a h))

theorem compl_exists (D : Grading F G L) (E : Grading F G V) (hE : GradedCompatible D E)
    (hcr : CompletelyReducible F L V) (U W : Submodule F V)
    (hU : LieStable (L := L) U) (hUg : GradedSubspace E U) (hWU : W ≤ U)
    (hW : LieStable (L := L) W) (hWg : GradedSubspace E W) :
    ∃ W' : Submodule F V, W' ≤ U ∧ LieStable (L := L) W' ∧ GradedSubspace E W' ∧
      Disjoint W W' ∧ W ⊔ W' = U := by
  obtain ⟨C, hC, hWC⟩ := hcr W hW
  let p : V →ₗ[F] V := W.projection C hWC
  have hp_mem : ∀ v, p v ∈ W := fun v => Submodule.projection_apply_mem hWC v
  have hp_id : ∀ w ∈ W, p w = w := fun w hw => Submodule.projection_apply_of_mem_left hWC hw
  have hp_C : ∀ c ∈ C, p c = 0 := fun c hc => Submodule.projection_apply_of_mem_right hWC hc
  have hp_lie : ∀ (a : L) v, p ⁅a, v⁆ = ⁅a, p v⁆ := by
    intro a v
    have hs : v - p v ∈ C := Submodule.sub_projection_mem hWC v
    have : ⁅a, v⁆ = ⁅a, p v⁆ + ⁅a, v - p v⁆ := by rw [← lie_add]; congr 1; abel
    rw [this, map_add, hp_id _ (hW a _ (hp_mem v)), hp_C _ (hC a _ hs), add_zero]
  set q := avgL E p with hq
  have hq_mem : ∀ v, q v ∈ W := avgL_mem E p W hWg hp_mem
  have hq_id : ∀ w ∈ W, q w = w := avgL_id E p W hWg hp_id
  have hq_lie : ∀ (a : L) v, q ⁅a, v⁆ = ⁅a, q v⁆ := avgL_lie D E hE p hp_lie
  refine ⟨U ⊓ LinearMap.ker q, inf_le_left, ?_, ?_, ?_, ?_⟩
  · intro a v hv
    refine ⟨hU a v hv.1, ?_⟩
    show q ⁅a, v⁆ = 0
    rw [hq_lie, show q v = 0 from hv.2, lie_zero]
  · intro v hv g
    refine ⟨hUg v hv.1 g, ?_⟩
    show q (E.decomp v g) = 0
    rw [← decomp_avgL, show avgL E p v = 0 from hv.2, map_zero, Finsupp.zero_apply]
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [← hq_id x hx]; exact hx'.2
  · apply le_antisymm (sup_le hWU inf_le_left)
    intro u hu
    rw [Submodule.mem_sup]
    refine ⟨q u, hq_mem u, u - q u, ⟨U.sub_mem hu (hWU (hq_mem u)), ?_⟩, by abel⟩
    show q (u - q u) = 0
    rw [map_sub, hq_id _ (hq_mem u), sub_self]

omit [Field F] [AddCommGroup V] [Module F V] in
theorem insert_indep {α : Type*} [CompleteLattice α] [IsModularLattice α]
    (S' : Set α) (W : α) (h : sSupIndep S') (hd : Disjoint W (sSup S')) (hW : W ∉ S') :
    sSupIndep (insert W S') := by
  intro a ha
  rcases ha with rfl | ha
  · rw [Set.insert_sdiff_of_mem _ (Set.mem_singleton _), Set.sdiff_singleton_eq_self hW]; exact hd
  · have haW : a ≠ W := fun e => hW (e ▸ ha)
    rw [Set.insert_sdiff_of_notMem _ (by simpa using haW.symm), sSup_insert]
    have h1 : Disjoint a (sSup (S' \ {a})) := h ha
    have h2 : Disjoint (a ⊔ sSup (S' \ {a})) W := by
      refine Disjoint.symm (hd.mono_right (sup_le (le_sSup ha) (sSup_le_sSup Set.sdiff_subset)))
    rw [sup_comm]
    exact h1.disjoint_sup_right_of_disjoint_sup_left h2

theorem decomp_exists [FiniteDimensional F V] (D : Grading F G L) (E : Grading F G V)
    (hE : GradedCompatible D E) (hcr : CompletelyReducible F L V) :
    ∀ n (U : Submodule F V), Module.finrank F U = n → LieStable (L := L) U → GradedSubspace E U →
      ∃ S : Finset (Submodule F V), sSupIndep (S : Set (Submodule F V)) ∧ sSup (S : Set (Submodule F V)) = U ∧
        ∀ P ∈ S, IrreducibleIn (L := L) (GradedSubspace E) P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn hU hUg
  by_cases hU0 : U = ⊥
  · exact ⟨∅, by simp, by simp [hU0], by simp⟩
  -- minimal nonzero stable graded W ≤ U
  have hex : ∃ k, ∃ W : Submodule F V, W ≤ U ∧ W ≠ ⊥ ∧ LieStable (L := L) W ∧ GradedSubspace E W ∧
      Module.finrank F W = k := ⟨_, U, le_rfl, hU0, hU, hUg, rfl⟩
  obtain ⟨W, hWU, hW0, hW, hWg, hWk⟩ := Nat.find_spec hex
  have hmin : ∀ W2 : Submodule F V, W2 ≤ U → W2 ≠ ⊥ → LieStable (L := L) W2 → GradedSubspace E W2 →
      Nat.find hex ≤ Module.finrank F W2 := fun W2 a b c d => Nat.find_min' hex ⟨W2, a, b, c, d, rfl⟩
  have hirr : IrreducibleIn (L := L) (GradedSubspace E) W := by
    refine ⟨hW, hWg, fun W2 h2 hs hg => ?_⟩
    by_cases h20 : W2 = ⊥
    · exact Or.inl h20
    · right
      exact Submodule.eq_of_le_of_finrank_le h2 (hWk ▸ hmin W2 (h2.trans hWU) h20 hs hg)
  obtain ⟨W', hW'U, hW', hW'g, hdis, hsup⟩ := compl_exists D E hE hcr U W hU hUg hWU hW hWg
  have hdim : Module.finrank F W' < n := by
    have := Submodule.finrank_sup_add_finrank_inf_eq W W'
    rw [hsup, hdis.eq_bot, finrank_bot, add_zero] at this
    have hpos : 0 < Module.finrank F W :=
      Nat.pos_of_ne_zero (fun h => hW0 (Submodule.finrank_eq_zero.mp h))
    omega
  obtain ⟨S', hS'i, hS's, hS'irr⟩ := ih _ hdim W' rfl hW' hW'g
  have hWS' : W ∉ S' := by
    intro hm
    have : W ≤ W' := hS's ▸ le_sSup (Finset.mem_coe.mpr hm)
    exact hW0 (by rw [← inf_eq_left.mpr this, hdis.eq_bot])
  refine ⟨insert W S', ?_, ?_, ?_⟩
  · rw [Finset.coe_insert]
    exact insert_indep _ W hS'i (hS's ▸ hdis) (by simpa using hWS')
  · rw [Finset.coe_insert, sSup_insert, hS's, hsup]
  · intro P hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact hirr
    · exact hS'irr P hP

end G61T

theorem solution {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]
    {V : Type*} [AddCommGroup V] [Module F V] [LieRingModule L V] [LieModule F L V]
    [CharZero F] [FiniteDimensional F V]
    {G : Type*} [Group G] (D : Grading F G L) (hD : GradedLie D)
    (E : Grading F G V) (hE : GradedCompatible D E)
    (hcr : CompletelyReducible F L V) :
    IrreducibleDecomposition (L := L) (GradedSubspace E) := by
  obtain ⟨S, hSi, hSs, hSirr⟩ := G61T.decomp_exists D E hE hcr _ ⊤ rfl
    (fun a v _ => Submodule.mem_top) (fun v _ g => Submodule.mem_top)
  let e := S.equivFin
  refine ⟨S.card, fun i => (e.symm i).1, ?_, ?_, fun i => hSirr _ (e.symm i).2⟩
  · have := ((sSupIndep_iff _).mp hSi).comp e.symm.injective
    exact this
  · rw [← hSs, sSup_eq_iSup']
    exact (e.symm.iSup_comp (g := fun x : (S : Set (Submodule F V)) => x.1))
