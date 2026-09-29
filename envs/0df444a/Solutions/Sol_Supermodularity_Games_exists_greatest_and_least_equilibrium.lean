-- Prove2me | solution 1 for Supermodularity.Games.exists_greatest_and_least_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:45:59.554045+00:00
-- url     : https://prove2.me/submissions/aef1cc7d-90e3-48bd-8cda-ad73e8ad12f8

import Mathlib
import Definitions.Def_Supermodularity_Games_IsSupermodularGame
import Definitions.Def_Supermodularity_Games_IsEquilibrium
import Definitions.Def_Supermodularity_Games_BestJointResponse
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace Supermodularity.Games

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}

lemma bj_update_sup (x x' : ∀ i, Fin (m i) → ℝ) (i : ι) (a b : Fin (m i) → ℝ) :
    Function.update x i a ⊔ Function.update x' i b = Function.update (x ⊔ x') i (a ⊔ b) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [Function.update_of_ne h]

lemma bj_update_inf (x x' : ∀ i, Fin (m i) → ℝ) (i : ι) (a b : Fin (m i) → ℝ) :
    Function.update x i a ⊓ Function.update x' i b = Function.update (x ⊓ x') i (a ⊓ b) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [Function.update_of_ne h]

/-- The feasible section `{y | update x i y ∈ S}` of a compact `S` is compact. -/
lemma bj_section_compact (S : Set (∀ i, Fin (m i) → ℝ)) (hS : IsCompact S)
    (x : ∀ i, Fin (m i) → ℝ) (i : ι) : IsCompact {y : Fin (m i) → ℝ | Function.update x i y ∈ S} := by
  have hL : IsClosed {z : ∀ i, Fin (m i) → ℝ | ∀ j, j ≠ i → z j = x j} := by
    have : {z : ∀ i, Fin (m i) → ℝ | ∀ j, j ≠ i → z j = x j} =
        ⋂ j ∈ {j | j ≠ i}, {z | z j = x j} := by ext z; simp
    rw [this]
    exact isClosed_biInter fun j _ => isClosed_eq (continuous_apply j) continuous_const
  have heq : {y : Fin (m i) → ℝ | Function.update x i y ∈ S} =
      (fun z : ∀ i, Fin (m i) → ℝ => z i) '' (S ∩ {z | ∀ j, j ≠ i → z j = x j}) := by
    ext y
    constructor
    · intro hy
      exact ⟨Function.update x i y, ⟨hy, fun j hj => Function.update_of_ne hj _ _⟩,
        Function.update_self _ _ _⟩
    · rintro ⟨z, ⟨hzS, hzL⟩, rfl⟩
      have : Function.update x i (z i) = z := by
        funext j
        rcases eq_or_ne j i with rfl | h
        · simp
        · rw [Function.update_of_ne h, hzL j h]
      show Function.update x i (z i) ∈ S
      rw [this]; exact hzS
  rw [heq]
  exact (hS.inter_right hL).image (continuous_apply i)

lemma bj_mem_proj {S : Set (∀ i, Fin (m i) → ℝ)} {x : ∀ i, Fin (m i) → ℝ} {i : ι}
    {y : Fin (m i) → ℝ} (h : Function.update x i y ∈ S) : y ∈ proj S i := ⟨x, h⟩

lemma bj_mem_projOthers {S : Set (∀ i, Fin (m i) → ℝ)} {x : ∀ i, Fin (m i) → ℝ} {i : ι}
    {y : Fin (m i) → ℝ} (h : Function.update x i y ∈ S) : x ∈ projOthers S i := ⟨y, h⟩

/-- Properties of a single player's best responses at a feasible profile. -/
lemma bj_br (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S})
    (x : ∀ i, Fin (m i) → ℝ) (hx : x ∈ S) (i : ι) :
    (BestResponse S f i x).Nonempty ∧ IsCompact (BestResponse S f i x) ∧
      ∀ ⦃a b⦄, a ∈ BestResponse S f i x → b ∈ BestResponse S f i x →
        a ⊔ b ∈ BestResponse S f i x ∧ a ⊓ b ∈ BestResponse S f i x := by
  set Sec := {y : Fin (m i) → ℝ | Function.update x i y ∈ S} with hSec
  have hxi : x i ∈ Sec := by show Function.update x i (x i) ∈ S; rw [Function.update_eq_self]; exact hx
  obtain ⟨y0, hy0, hmax⟩ := (husc i x).exists_isMaxOn ⟨x i, hxi⟩ (bj_section_compact S hScompact x i)
  have hBR : BestResponse S f i x =
      Sec ∩ (fun y => f i (Function.update x i y)) ⁻¹' Set.Ici (f i (Function.update x i y0)) := by
    ext y
    simp only [BestResponse, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 y0 hy0⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun z hz => (isMaxOn_iff.mp hmax z hz).trans h2⟩
  refine ⟨⟨y0, ?_⟩, ?_, fun a b ha hb => ?_⟩
  · rw [hBR]; exact ⟨hy0, Set.mem_preimage.mpr (Set.mem_Ici.mpr le_rfl)⟩
  · obtain ⟨v, hv, hvEq⟩ := upperSemicontinuousOn_iff_preimage_Ici.mp (husc i x)
      (f i (Function.update x i y0))
    rw [hBR, hvEq]
    exact (bj_section_compact S hScompact x i).inter_right hv
  · obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have hsup : Function.update x i (a ⊔ b) ∈ S := by
      have := hgame.sublattice.supClosed ha1 hb1
      rwa [bj_update_sup, sup_idem] at this
    have hinf : Function.update x i (a ⊓ b) ∈ S := by
      have := hgame.sublattice.infClosed ha1 hb1
      rwa [bj_update_inf, inf_idem] at this
    have hsm := hgame.supermodular i x (bj_mem_projOthers hx') (bj_mem_proj ha1) (bj_mem_proj hb1)
    have e1 := ha2 (a ⊔ b) hsup
    have e2 := hb2 (a ⊓ b) hinf
    have e3 := ha2 b hb1
    have e4 := ha2 (a ⊓ b) hinf
    have e5 := hb2 (a ⊔ b) hsup
    have e6 := hb2 a ha1
    simp only at hsm
    refine ⟨⟨hsup, fun z hz => ?_⟩, ⟨hinf, fun z hz => ?_⟩⟩
    · have := ha2 z hz; linarith
    · have := ha2 z hz; linarith
  where hx' : Function.update x i (x i) ∈ S := by rw [Function.update_eq_self]; exact hx


/-- Topkis's monotonicity argument for one player. -/
lemma bj_incr (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S})
    {x x' : ∀ i, Fin (m i) → ℝ} (hx : x ∈ S) (hx' : x' ∈ S) (hle : x ≤ x') (i : ι)
    {A B : Fin (m i) → ℝ} (hA : A ∈ BestResponse S f i x) (hB : B ∈ BestResponse S f i x') :
    A ⊓ B ∈ BestResponse S f i x ∧ A ⊔ B ∈ BestResponse S f i x' := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq
    have := (bj_br S f hgame hScompact husc x hx i).2.2 hA hB
    exact ⟨this.2, this.1⟩
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  have hinf : Function.update x i (A ⊓ B) ∈ S := by
    have := hgame.sublattice.infClosed hA1 hB1
    rwa [bj_update_inf, inf_eq_left.mpr hle] at this
  have hsup : Function.update x' i (A ⊔ B) ∈ S := by
    have := hgame.sublattice.supClosed hA1 hB1
    rwa [bj_update_sup, sup_eq_right.mpr hle] at this
  have hsm := hgame.supermodular i x (bj_mem_projOthers hA1) (bj_mem_proj hA1) (bj_mem_proj hB1)
  have hid := hgame.increasing_differences i hlt
    ⟨Set.mk_mem_prod (bj_mem_proj hB1) (bj_mem_projOthers hA1),
      Set.mk_mem_prod (bj_mem_proj hB1) (bj_mem_projOthers hB1)⟩
    ⟨Set.mk_mem_prod (bj_mem_proj hsup) (bj_mem_projOthers hA1),
      Set.mk_mem_prod (bj_mem_proj hsup) (bj_mem_projOthers hB1)⟩
    (le_sup_right : B ≤ A ⊔ B)
  have o1 := hB2 (A ⊔ B) hsup
  have o2 := hA2 (A ⊓ B) hinf
  simp only at hsm hid
  refine ⟨⟨hinf, fun z hz => ?_⟩, ⟨hsup, fun z hz => ?_⟩⟩
  · have := hA2 z hz; linarith
  · have := hB2 z hz; linarith

theorem bj_main (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S}) :
    (∀ x ∈ S, (BestJointResponse S f x).Nonempty ∧ IsCompact (BestJointResponse S f x) ∧
      IsSublattice (BestJointResponse S f x)) ∧
    ∀ ⦃x x' : ∀ i, Fin (m i) → ℝ⦄, x ∈ S → x' ∈ S → x ≤ x' →
      Supermodularity.Lattices.InducedSetOrder (BestJointResponse S f x)
        (BestJointResponse S f x') := by
  have hBJR : ∀ x, BestJointResponse S f x = Set.univ.pi (fun i => BestResponse S f i x) := by
    intro x; ext y; simp [BestJointResponse, Set.mem_univ_pi]
  refine ⟨fun x hx => ?_, fun x x' hx hx' hle => ?_⟩
  · have hbr := fun i => bj_br S f hgame hScompact husc x hx i
    rw [hBJR]
    refine ⟨Set.univ_pi_nonempty_iff.mpr fun i => (hbr i).1,
      isCompact_univ_pi fun i => (hbr i).2.1, ⟨fun a ha b hb => ?_, fun a ha b hb => ?_⟩⟩
    · intro i _
      exact ((hbr i).2.2 (ha i (Set.mem_univ i)) (hb i (Set.mem_univ i))).1
    · intro i _
      exact ((hbr i).2.2 (ha i (Set.mem_univ i)) (hb i (Set.mem_univ i))).2
  · intro a ha b hb
    rw [hBJR] at ha hb
    rw [hBJR, hBJR]
    refine ⟨fun i _ => ?_, fun i _ => ?_⟩
    · exact (bj_incr S f hgame hScompact husc hx hx' hle i (ha i (Set.mem_univ i))
        (hb i (Set.mem_univ i))).1
    · exact (bj_incr S f hgame hScompact husc hx hx' hle i (ha i (Set.mem_univ i))
        (hb i (Set.mem_univ i))).2


/-- Every nonempty subset of a compact sup-closed set has its least upper bound in the set. -/
lemma sm_lub {S B : Set (∀ i, Fin (m i) → ℝ)} (hS : IsCompact S) (hsup : SupClosed S)
    (hBS : B ⊆ S) (hB : B.Nonempty) : ∃ z ∈ S, IsLUB B z := by
  classical
  have hK : IsCompact (closure B) :=
    hS.of_isClosed_subset isClosed_closure (closure_minimal hBS hS.isClosed)
  have hKne : (closure B).Nonempty := hB.mono subset_closure
  have hmax : ∀ c : (Σ i, Fin (m i)), ∃ s ∈ closure B,
      IsMaxOn (fun x : ∀ i, Fin (m i) → ℝ => x c.1 c.2) (closure B) s :=
    fun c => hK.exists_isMaxOn hKne
      ((continuous_apply c.2).comp (continuous_apply c.1)).continuousOn
  choose s hsK hsmax using hmax
  rcases isEmpty_or_nonempty (Σ i, Fin (m i)) with hc | hc
  · obtain ⟨b, hb⟩ := hB
    refine ⟨b, hBS hb, fun x _ => le_of_eq ?_, fun a _ => le_of_eq ?_⟩ <;>
      (funext i k; exact isEmptyElim (⟨i, k⟩ : Σ i, Fin (m i)))
  · refine ⟨Finset.univ.sup' Finset.univ_nonempty s,
      hsup.finsetSup'_mem Finset.univ_nonempty fun c _ =>
        closure_minimal hBS hS.isClosed (hsK c), ?_, ?_⟩
    · intro b hb i k
      have h1 : b i k ≤ s ⟨i, k⟩ i k := hsmax ⟨i, k⟩ (subset_closure hb)
      have h2 : s ⟨i, k⟩ ≤ Finset.univ.sup' Finset.univ_nonempty s :=
        Finset.le_sup' s (Finset.mem_univ _)
      exact h1.trans (h2 i k)
    · intro a ha
      apply Finset.sup'_le
      intro c _
      have : closure B ⊆ {x | x ≤ a} :=
        closure_minimal (fun b hb => ha hb) (isClosed_le continuous_id continuous_const)
      exact this (hsK c)

/-- Every nonempty subset of a compact inf-closed set has its greatest lower bound in the set. -/
lemma sm_glb {S B : Set (∀ i, Fin (m i) → ℝ)} (hS : IsCompact S) (hinf : InfClosed S)
    (hBS : B ⊆ S) (hB : B.Nonempty) : ∃ z ∈ S, IsGLB B z := by
  classical
  have hK : IsCompact (closure B) :=
    hS.of_isClosed_subset isClosed_closure (closure_minimal hBS hS.isClosed)
  have hKne : (closure B).Nonempty := hB.mono subset_closure
  have hmin : ∀ c : (Σ i, Fin (m i)), ∃ s ∈ closure B,
      IsMinOn (fun x : ∀ i, Fin (m i) → ℝ => x c.1 c.2) (closure B) s :=
    fun c => hK.exists_isMinOn hKne
      ((continuous_apply c.2).comp (continuous_apply c.1)).continuousOn
  choose s hsK hsmin using hmin
  rcases isEmpty_or_nonempty (Σ i, Fin (m i)) with hc | hc
  · obtain ⟨b, hb⟩ := hB
    refine ⟨b, hBS hb, fun x _ => le_of_eq ?_, fun a _ => le_of_eq ?_⟩ <;>
      (funext i k; exact isEmptyElim (⟨i, k⟩ : Σ i, Fin (m i)))
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty s,
      hinf.finsetInf'_mem Finset.univ_nonempty fun c _ =>
        closure_minimal hBS hS.isClosed (hsK c), ?_, ?_⟩
    · intro b hb i k
      have h1 : s ⟨i, k⟩ i k ≤ b i k := hsmin ⟨i, k⟩ (subset_closure hb)
      have h2 : Finset.univ.inf' Finset.univ_nonempty s ≤ s ⟨i, k⟩ :=
        Finset.inf'_le s (Finset.mem_univ _)
      exact (h2 i k).trans h1
    · intro a ha
      apply Finset.le_inf'
      intro c _
      have : closure B ⊆ {x | a ≤ x} :=
        closure_minimal (fun b hb => ha hb) (isClosed_le continuous_const continuous_id)
      exact this (hsK c)

lemma sm_eq_iff {S : Set (∀ i, Fin (m i) → ℝ)} {f : ι → (∀ i, Fin (m i) → ℝ) → ℝ}
    (x : ∀ i, Fin (m i) → ℝ) :
    IsEquilibrium S f x ↔ x ∈ S ∧ x ∈ BestJointResponse S f x := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun i => ⟨by rw [Function.update_eq_self]; exact hx, fun z hz => ?_⟩⟩
    rw [Function.update_eq_self]; exact h i z hz
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun i y hy => ?_⟩
    have := (h i).2 y hy
    rwa [Function.update_eq_self] at this

/-- A best response lying above a feasible point is feasible. -/
lemma sm_up_mem {S : Set (∀ i, Fin (m i) → ℝ)} (hsup : SupClosed S)
    {x y : ∀ i, Fin (m i) → ℝ} (hx : x ∈ S) (hxy : x ≤ y)
    (hy : ∀ i, Function.update x i (y i) ∈ S) : y ∈ S := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : y = x := funext fun i => isEmptyElim i
    rw [this]; exact hx
  · have hsup' : Finset.univ.sup' Finset.univ_nonempty (fun i => Function.update x i (y i)) = y := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro i _ j
        rcases eq_or_ne j i with rfl | h
        · simp
        · rw [Function.update_of_ne h]; exact hxy j
      · intro j
        calc y j = Function.update x j (y j) j := by simp
          _ ≤ (Finset.univ.sup' Finset.univ_nonempty (fun i => Function.update x i (y i))) j :=
            Finset.le_sup' (fun i => Function.update x i (y i)) (Finset.mem_univ j) j
    rw [← hsup']
    exact hsup.finsetSup'_mem Finset.univ_nonempty fun i _ => hy i

/-- A best response lying below a feasible point is feasible. -/
lemma sm_down_mem {S : Set (∀ i, Fin (m i) → ℝ)} (hinf : InfClosed S)
    {x y : ∀ i, Fin (m i) → ℝ} (hx : x ∈ S) (hyx : y ≤ x)
    (hy : ∀ i, Function.update x i (y i) ∈ S) : y ∈ S := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : y = x := funext fun i => isEmptyElim i
    rw [this]; exact hx
  · have hinf' : Finset.univ.inf' Finset.univ_nonempty (fun i => Function.update x i (y i)) = y := by
      apply le_antisymm
      · intro j
        calc (Finset.univ.inf' Finset.univ_nonempty (fun i => Function.update x i (y i))) j
            ≤ Function.update x j (y j) j :=
              Finset.inf'_le (fun i => Function.update x i (y i)) (Finset.mem_univ j) j
          _ = y j := by simp
      · apply Finset.le_inf'
        intro i _ j
        rcases eq_or_ne j i with rfl | h
        · simp
        · rw [Function.update_of_ne h]; exact hyx j
    rw [← hinf']
    exact hinf.finsetInf'_mem Finset.univ_nonempty fun i _ => hy i

/-- The least equilibrium above a point `u`, a Tarski-type argument. -/
lemma sm_lfp (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S})
    (u : ∀ i, Fin (m i) → ℝ) (h1 : ∃ x0 ∈ S, u ≤ x0)
    (h2 : ∀ x ∈ S, u ≤ x → ∃ y ∈ BestJointResponse S f x, u ≤ y) :
    ∃ e, IsEquilibrium S f e ∧ u ≤ e ∧ ∀ e', IsEquilibrium S f e' → u ≤ e' → e ≤ e' := by
  obtain ⟨hY, hmono⟩ := bj_main S f hgame hScompact husc
  have hsub := hgame.sublattice
  obtain ⟨x0, hx0S, hux0⟩ := h1
  have hleast : ∀ x ∈ S, u ≤ x → ∃ l, (l ∈ BestJointResponse S f x ∧ u ≤ l) ∧
      ∀ y, y ∈ BestJointResponse S f x → u ≤ y → l ≤ y := by
    intro x hx hux
    obtain ⟨hne, hcpt, hsl⟩ := hY x hx
    have hY'c : IsCompact {y | y ∈ BestJointResponse S f x ∧ u ≤ y} :=
      hcpt.inter_right (isClosed_le continuous_const continuous_id)
    have hY'inf : InfClosed {y | y ∈ BestJointResponse S f x ∧ u ≤ y} :=
      fun a ha b hb => ⟨hsl.infClosed ha.1 hb.1, le_inf ha.2 hb.2⟩
    obtain ⟨y0, hy0, huy0⟩ := h2 x hx hux
    obtain ⟨l, hl, hlglb⟩ := sm_glb hY'c hY'inf subset_rfl ⟨y0, hy0, huy0⟩
    exact ⟨l, hl, fun y hy huy => hlglb.1 ⟨hy, huy⟩⟩
  obtain ⟨x1, hx1S, hx1⟩ := sm_lub hScompact hsub.supClosed subset_rfl ⟨x0, hx0S⟩
  have hYtop : ∀ x y, y ∈ BestJointResponse S f x → y ≤ x1 := by
    intro x y hy i
    have := hx1.1 (hy i).1
    simpa using this i
  have hux1 : u ≤ x1 := hux0.trans (hx1.1 hx0S)
  set B := {x | x ∈ S ∧ u ≤ x ∧ ∃ y, (y ∈ BestJointResponse S f x ∧ u ≤ y) ∧ y ≤ x} with hB
  have hx1B : x1 ∈ B := by
    obtain ⟨l, hl, -⟩ := hleast x1 hx1S hux1
    exact ⟨hx1S, hux1, l, hl, hYtop x1 l hl.1⟩
  obtain ⟨xs, hxsS, hxs⟩ := sm_glb hScompact hsub.infClosed (fun x hx => hx.1) ⟨x1, hx1B⟩
  have huxs : u ≤ xs := hxs.2 (fun x hx => hx.2.1)
  obtain ⟨ys, hys, hysmin⟩ := hleast xs hxsS huxs
  have hys_lb : ys ∈ lowerBounds B := by
    intro x hx
    obtain ⟨hxS, hux, y, hy, hyx⟩ := hx
    have hle : xs ≤ x := hxs.1 ⟨hxS, hux, y, hy, hyx⟩
    have hmeet := (hmono hxsS hxS hle hys.1 hy.1).1
    have := hysmin _ hmeet (le_inf hys.2 hy.2)
    exact (this.trans inf_le_right).trans hyx
  have hys_le : ys ≤ xs := hxs.2 hys_lb
  have hysS : ys ∈ S := sm_down_mem hsub.infClosed hxsS hys_le (fun i => (hys.1 i).1)
  have hysB : ys ∈ B := by
    obtain ⟨y'', hy'', -⟩ := hleast ys hysS hys.2
    refine ⟨hysS, hys.2, y'' ⊓ ys, ⟨(hmono hysS hxsS hys_le hy''.1 hys.1).1,
      le_inf hy''.2 hys.2⟩, inf_le_right⟩
  have heq : xs = ys := le_antisymm (hxs.1 hysB) hys_le
  have hfix : xs ∈ BestJointResponse S f xs := by
    have h := hys.1; rw [← heq] at h; exact h
  refine ⟨xs, (sm_eq_iff xs).mpr ⟨hxsS, hfix⟩, huxs, fun e' he' hue' => ?_⟩
  obtain ⟨he'S, he'Y⟩ := (sm_eq_iff e').mp he'
  exact hxs.1 ⟨he'S, hue', e', ⟨he'Y, hue'⟩, le_rfl⟩

/-- The greatest equilibrium below a point `v` (dual argument). -/
lemma sm_gfp (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S})
    (v : ∀ i, Fin (m i) → ℝ) (h1 : ∃ x0 ∈ S, x0 ≤ v)
    (h2 : ∀ x ∈ S, x ≤ v → ∃ y ∈ BestJointResponse S f x, y ≤ v) :
    ∃ e, IsEquilibrium S f e ∧ e ≤ v ∧ ∀ e', IsEquilibrium S f e' → e' ≤ v → e' ≤ e := by
  obtain ⟨hY, hmono⟩ := bj_main S f hgame hScompact husc
  have hsub := hgame.sublattice
  obtain ⟨x0, hx0S, hx0v⟩ := h1
  have hgreat : ∀ x ∈ S, x ≤ v → ∃ g, (g ∈ BestJointResponse S f x ∧ g ≤ v) ∧
      ∀ y, y ∈ BestJointResponse S f x → y ≤ v → y ≤ g := by
    intro x hx hxv
    obtain ⟨hne, hcpt, hsl⟩ := hY x hx
    have hY'c : IsCompact {y | y ∈ BestJointResponse S f x ∧ y ≤ v} :=
      hcpt.inter_right (isClosed_le continuous_id continuous_const)
    have hY'sup : SupClosed {y | y ∈ BestJointResponse S f x ∧ y ≤ v} :=
      fun a ha b hb => ⟨hsl.supClosed ha.1 hb.1, sup_le ha.2 hb.2⟩
    obtain ⟨y0, hy0, hy0v⟩ := h2 x hx hxv
    obtain ⟨g, hg, hglub⟩ := sm_lub hY'c hY'sup subset_rfl ⟨y0, hy0, hy0v⟩
    exact ⟨g, hg, fun y hy hyv => hglub.1 ⟨hy, hyv⟩⟩
  obtain ⟨x1, hx1S, hx1⟩ := sm_glb hScompact hsub.infClosed subset_rfl ⟨x0, hx0S⟩
  have hYbot : ∀ x y, y ∈ BestJointResponse S f x → x1 ≤ y := by
    intro x y hy i
    have := hx1.1 (hy i).1
    simpa using this i
  have hx1v : x1 ≤ v := (hx1.1 hx0S).trans hx0v
  set B := {x | x ∈ S ∧ x ≤ v ∧ ∃ y, (y ∈ BestJointResponse S f x ∧ y ≤ v) ∧ x ≤ y} with hB
  have hx1B : x1 ∈ B := by
    obtain ⟨g, hg, -⟩ := hgreat x1 hx1S hx1v
    exact ⟨hx1S, hx1v, g, hg, hYbot x1 g hg.1⟩
  obtain ⟨xs, hxsS, hxs⟩ := sm_lub hScompact hsub.supClosed (fun x hx => hx.1) ⟨x1, hx1B⟩
  have hxsv : xs ≤ v := hxs.2 (fun x hx => hx.2.1)
  obtain ⟨ys, hys, hysmax⟩ := hgreat xs hxsS hxsv
  have hys_ub : ys ∈ upperBounds B := by
    intro x hx
    obtain ⟨hxS, hxv, y, hy, hxy⟩ := hx
    have hle : x ≤ xs := hxs.1 ⟨hxS, hxv, y, hy, hxy⟩
    have hjoin := (hmono hxS hxsS hle hy.1 hys.1).2
    have := hysmax _ hjoin (sup_le hy.2 hys.2)
    exact hxy.trans (le_sup_left.trans this)
  have hxs_le : xs ≤ ys := hxs.2 hys_ub
  have hysS : ys ∈ S := sm_up_mem hsub.supClosed hxsS hxs_le (fun i => (hys.1 i).1)
  have hysB : ys ∈ B := by
    obtain ⟨y'', hy'', -⟩ := hgreat ys hysS hys.2
    refine ⟨hysS, hys.2, ys ⊔ y'', ⟨(hmono hxsS hysS hxs_le hys.1 hy''.1).2,
      sup_le hys.2 hy''.2⟩, le_sup_left⟩
  have heq : xs = ys := le_antisymm hxs_le (hxs.1 hysB)
  have hfix : xs ∈ BestJointResponse S f xs := by
    have h := hys.1; rw [← heq] at h; exact h
  refine ⟨xs, (sm_eq_iff xs).mpr ⟨hxsS, hfix⟩, hxsv, fun e' he' he'v => ?_⟩
  obtain ⟨he'S, he'Y⟩ := (sm_eq_iff e').mp he'
  exact hxs.1 ⟨he'S, he'v, e', ⟨he'Y, he'v⟩, le_rfl⟩

theorem sm_main {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → ℕ} (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hSne : S.Nonempty) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S}) :
    {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium S f x'}.Nonempty ∧
    (∃ g, IsGreatest {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium S f x'} g) ∧
    (∃ l, IsLeast {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium S f x'} l) ∧
    (∀ F : Set {x' : ∀ i, Fin (m i) → ℝ // IsEquilibrium S f x'}, F.Nonempty → ∃ b, IsLUB F b) ∧
    (∀ F : Set {x' : ∀ i, Fin (m i) → ℝ // IsEquilibrium S f x'}, F.Nonempty → ∃ b, IsGLB F b) := by
  obtain ⟨hY, hmono⟩ := bj_main S f hgame hScompact husc
  have hsub := hgame.sublattice
  obtain ⟨x1, hx1S, hx1⟩ := sm_lub hScompact hsub.supClosed subset_rfl hSne
  obtain ⟨x0, hx0S, hx0⟩ := sm_glb hScompact hsub.infClosed subset_rfl hSne
  have hYtop : ∀ x y, y ∈ BestJointResponse S f x → y ≤ x1 := by
    intro x y hy i
    have := hx1.1 (hy i).1
    simpa using this i
  have hYbot : ∀ x y, y ∈ BestJointResponse S f x → x0 ≤ y := by
    intro x y hy i
    have := hx0.1 (hy i).1
    simpa using this i
  obtain ⟨g, hg, -, hgmax⟩ := sm_gfp S f hgame hScompact husc x1 ⟨x1, hx1S, le_rfl⟩
    (fun x hx _ => by obtain ⟨y, hy⟩ := (hY x hx).1; exact ⟨y, hy, hYtop x y hy⟩)
  obtain ⟨l, hl, -, hlmin⟩ := sm_lfp S f hgame hScompact husc x0 ⟨x0, hx0S, le_rfl⟩
    (fun x hx _ => by obtain ⟨y, hy⟩ := (hY x hx).1; exact ⟨y, hy, hYbot x y hy⟩)
  refine ⟨⟨g, hg⟩, ⟨g, hg, fun e he => hgmax e he (hx1.1 he.1)⟩,
    ⟨l, hl, fun e he => hlmin e he (hx0.1 he.1)⟩, fun F hF => ?_, fun F hF => ?_⟩
  · -- least upper bound of a nonempty family of equilibria
    have hF'S : Subtype.val '' F ⊆ S := by
      rintro _ ⟨e, -, rfl⟩; exact e.2.1
    obtain ⟨u, huS, hu⟩ := sm_lub hScompact hsub.supClosed hF'S (hF.image _)
    have h2 : ∀ x ∈ S, u ≤ x → ∃ y ∈ BestJointResponse S f x, u ≤ y := by
      intro x hx hux
      obtain ⟨hne, hcpt, hsl⟩ := hY x hx
      obtain ⟨yb, hyb, hyblub⟩ := sm_lub hcpt hsl.supClosed subset_rfl hne
      refine ⟨yb, hyb, hu.2 ?_⟩
      rintro _ ⟨e, he, rfl⟩
      obtain ⟨heS, heY⟩ := (sm_eq_iff e.1).mp e.2
      have hex : e.1 ≤ x := (hu.1 ⟨e, he, rfl⟩).trans hux
      have := (hmono heS hx hex heY hyb).2
      exact le_sup_left.trans (hyblub.1 this)
    obtain ⟨b, hb, hub, hbmin⟩ := sm_lfp S f hgame hScompact husc u ⟨u, huS, le_rfl⟩ h2
    refine ⟨⟨b, hb⟩, fun e he => ?_, fun b' hb' => ?_⟩
    · exact (hu.1 ⟨e, he, rfl⟩).trans hub
    · have : u ≤ b'.1 := hu.2 (by rintro _ ⟨e, he, rfl⟩; exact hb' he)
      exact hbmin b'.1 b'.2 this
  · -- greatest lower bound of a nonempty family of equilibria
    have hF'S : Subtype.val '' F ⊆ S := by
      rintro _ ⟨e, -, rfl⟩; exact e.2.1
    obtain ⟨v, hvS, hv⟩ := sm_glb hScompact hsub.infClosed hF'S (hF.image _)
    have h2 : ∀ x ∈ S, x ≤ v → ∃ y ∈ BestJointResponse S f x, y ≤ v := by
      intro x hx hxv
      obtain ⟨hne, hcpt, hsl⟩ := hY x hx
      obtain ⟨yb, hyb, hybglb⟩ := sm_glb hcpt hsl.infClosed subset_rfl hne
      refine ⟨yb, hyb, hv.2 ?_⟩
      rintro _ ⟨e, he, rfl⟩
      obtain ⟨heS, heY⟩ := (sm_eq_iff e.1).mp e.2
      have hxe : x ≤ e.1 := hxv.trans (hv.1 ⟨e, he, rfl⟩)
      have := (hmono hx heS hxe hyb heY).1
      exact (hybglb.1 this).trans inf_le_right
    obtain ⟨b, hb, hbv, hbmax⟩ := sm_gfp S f hgame hScompact husc v ⟨v, hvS, le_rfl⟩ h2
    refine ⟨⟨b, hb⟩, fun e he => ?_, fun b' hb' => ?_⟩
    · exact hbv.trans (hv.1 ⟨e, he, rfl⟩)
    · have : b'.1 ≤ v := hv.2 (by rintro _ ⟨e, he, rfl⟩; exact hb' he)
      exact hbmax b'.1 b'.2 this


end Supermodularity.Games

open Supermodularity.Games

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → ℕ} (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hSne : S.Nonempty) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S}) :
    {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium S f x'}.Nonempty ∧
    (∃ g, IsGreatest {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium S f x'} g) ∧
    (∃ l, IsLeast {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium S f x'} l) ∧
    (∀ F : Set {x' : ∀ i, Fin (m i) → ℝ // IsEquilibrium S f x'}, F.Nonempty → ∃ b, IsLUB F b) ∧
    (∀ F : Set {x' : ∀ i, Fin (m i) → ℝ // IsEquilibrium S f x'}, F.Nonempty → ∃ b, IsGLB F b) := by
  exact sm_main S f hgame hSne hScompact husc
