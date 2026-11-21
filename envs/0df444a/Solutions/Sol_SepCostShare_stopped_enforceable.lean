-- Prove2me | solution 1 for SepCostShare.stopped_enforceable
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:06:18.749365+00:00
-- url     : https://prove2.me/submissions/08b49add-2558-4879-a1cf-69b0c9a3829f

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Protocol
import Definitions.Def_SepCostShare_Deviation
import Definitions.Def_SepCostShare_Algorithm
set_option autoImplicit false

namespace Aux_SepCostShare_stopped_enforceable

open SepCostShare

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

noncomputable def chat (G : MatroidGame N E) (g : E) (U : Finset N) : ℝ :=
  if U.Nonempty then G.c g U else 0

theorem cost_eq (G : MatroidGame N E) (B : N → Finset E) :
    G.cost B = ∑ g, chat G g (G.users g B) + ∑ j, ∑ g ∈ B j, G.d j g := by
  unfold MatroidGame.cost chat
  rw [Finset.sum_filter]

theorem deltaBar_congr (G : MatroidGame N E) {B B' : N → Finset E} {i : N} {e : E}
    (h : B i = B' i) : G.deltaBar B i e = G.deltaBar B' i e := by
  unfold MatroidGame.deltaBar MatroidGame.alts
  rw [h]

theorem mem_users (G : MatroidGame N E) (B : N → Finset E) (g : E) (j : N) :
    j ∈ G.users g B ↔ g ∈ B j := by
  simp [MatroidGame.users]

theorem alts_base (G : MatroidGame N E) {B : N → Finset E} {i : N} {e f : E}
    (hf : f ∈ G.alts B i e) : (G.M i).IsBase (↑(insert f ((B i).erase e)) : Set E) := by
  unfold MatroidGame.alts at hf
  simpa using hf

theorem not_mem_of_alt (G : MatroidGame N E) {B : N → Finset E} (hB : G.IsProfile B) {i : N}
    {e f : E} (hei : e ∈ B i) (hfe : f ≠ e) (hf : f ∈ G.alts B i e) : f ∉ B i := by
  intro hf'
  have hbase := alts_base G hf
  have h1 : insert f ((B i).erase e) = (B i).erase e :=
    Finset.insert_eq_of_mem (Finset.mem_erase.mpr ⟨hfe, hf'⟩)
  rw [h1] at hbase
  have h2 := hbase.eq_of_subset_isBase (hB i) (by
    intro x hx
    simp only [Finset.mem_coe] at hx ⊢
    exact Finset.mem_of_mem_erase hx)
  have h3 : (B i).erase e = B i := by exact_mod_cast h2
  have : e ∉ (B i).erase e := Finset.notMem_erase e (B i)
  rw [h3] at this
  exact this hei

section Swap

variable (G : MatroidGame N E) (B : N → Finset E) (i : N) (e f : E)

theorem users_swap_e (hfe : f ≠ e) :
    G.users e (G.swap B i e f) = (G.users e B).erase i := by
  ext j
  rw [mem_users, Finset.mem_erase, mem_users]
  unfold MatroidGame.swap
  by_cases hj : j = i
  · subst hj
    simp [Function.update_self, Ne.symm hfe]
  · simp [Function.update_of_ne hj, hj]

theorem users_swap_f :
    G.users f (G.swap B i e f) = insert i (G.users f B) := by
  ext j
  rw [mem_users, Finset.mem_insert, mem_users]
  unfold MatroidGame.swap
  by_cases hj : j = i
  · subst hj
    simp [Function.update_self]
  · simp [Function.update_of_ne hj, hj]

theorem users_swap_other (g : E) (hge : g ≠ e) (hgf : g ≠ f) :
    G.users g (G.swap B i e f) = G.users g B := by
  ext j
  rw [mem_users, mem_users]
  unfold MatroidGame.swap
  by_cases hj : j = i
  · subst hj
    simp [Function.update_self, hge, hgf]
  · simp [Function.update_of_ne hj]

theorem swap_ne (j : N) (hj : j ≠ i) : G.swap B i e f j = B j := by
  unfold MatroidGame.swap
  exact Function.update_of_ne hj _ _

theorem swap_self : G.swap B i e f i = insert f ((B i).erase e) := by
  unfold MatroidGame.swap
  exact Function.update_self _ _ _

end Swap

/-- cost change of one swap -/
theorem cost_swap (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E) (i : N)
    (e f : E) (hfe : f ≠ e) (hei : e ∈ B i) (hfi : f ∉ B i) :
    G.cost (G.swap B i e f) ≤ G.cost B + (chat G e ((G.users e B).erase i) -
      chat G e (G.users e B)) + G.pi i f - G.d i e := by
  rw [cost_eq, cost_eq]
  -- the c-part
  have hc : ∑ g, chat G g (G.users g (G.swap B i e f)) =
      ∑ g, chat G g (G.users g B) +
        ((chat G e ((G.users e B).erase i) - chat G e (G.users e B)) +
          (chat G f (insert i (G.users f B)) - chat G f (G.users f B))) := by
    have h0 : ∑ g, (chat G g (G.users g (G.swap B i e f)) - chat G g (G.users g B)) =
        (chat G e ((G.users e B).erase i) - chat G e (G.users e B)) +
          (chat G f (insert i (G.users f B)) - chat G f (G.users f B)) := by
      rw [Finset.sum_eq_add_of_mem e f (Finset.mem_univ e) (Finset.mem_univ f) (Ne.symm hfe)]
      · rw [users_swap_e G B i e f hfe, users_swap_f G B i e f]
      · intro g _ hg
        rw [users_swap_other G B i e f g hg.1 hg.2, sub_self]
    rw [← h0, Finset.sum_sub_distrib]
    ring
  -- the d-part
  have hd : ∑ j, ∑ g ∈ G.swap B i e f j, G.d j g =
      ∑ j, ∑ g ∈ B j, G.d j g + (G.d i f - G.d i e) := by
    have h0 : ∑ j, (∑ g ∈ G.swap B i e f j, G.d j g - ∑ g ∈ B j, G.d j g) =
        G.d i f - G.d i e := by
      rw [Finset.sum_eq_single i]
      · rw [swap_self, Finset.sum_insert (fun h => hfi (Finset.mem_of_mem_erase h)),
          Finset.sum_erase_eq_sub hei]
        ring
      · intro j _ hj
        rw [swap_ne G B i e f j hj, sub_self]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [← h0, Finset.sum_sub_distrib]
    ring
  rw [hc, hd]
  -- subadditivity at f
  have hsub : chat G f (insert i (G.users f B)) - chat G f (G.users f B) ≤ G.c f {i} := by
    have hiU : i ∉ G.users f B := by rw [mem_users]; exact hfi
    have hne : (insert i (G.users f B)).Nonempty := Finset.insert_nonempty _ _
    unfold chat
    rw [if_pos hne]
    by_cases hU : (G.users f B).Nonempty
    · rw [if_pos hU]
      have hss : G.users f B ⊂ Finset.univ :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,
          fun h => hiU (h ▸ Finset.mem_univ i)⟩
      have := hG.2 f (G.users f B) hss i
      linarith
    · rw [if_neg hU]
      rw [Finset.not_nonempty_iff_eq_empty] at hU
      rw [hU]
      simp
  unfold MatroidGame.pi
  linarith

/-- Hall-type exchange matching between two bases. -/
theorem base_matching {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α) (B T : Finset α)
    (hB : M.IsBase (↑B : Set α)) (hT : M.IsBase (↑T : Set α)) :
    ∃ φ : α → α, (∀ e ∈ B \ T, φ e ∈ T \ B ∧ M.IsBase (↑(insert (φ e) (B.erase e)) : Set α)) ∧
      Set.InjOn φ (↑(B \ T) : Set α) := by
  classical
  let t : {e // e ∈ B \ T} → Finset α := fun x =>
    (T \ B).filter (fun f => M.IsBase (↑(insert f (B.erase x.1)) : Set α))
  have hall : ∀ s : Finset {e // e ∈ B \ T}, s.card ≤ (s.biUnion t).card := by
    intro s
    by_contra hlt
    push_neg at hlt
    have hsne : s.Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨X, hXd⟩ : ∃ X : Finset α, X = s.map ⟨Subtype.val, Subtype.val_injective⟩ := ⟨_, rfl⟩
    have hXc : X.card = s.card := by rw [hXd]; exact Finset.card_map _
    have hXB : X ⊆ B := by
      intro y hy
      rw [hXd, Finset.mem_map] at hy
      obtain ⟨x, _, rfl⟩ := hy
      exact (Finset.mem_sdiff.mp x.2).1
    obtain ⟨A, hAd⟩ : ∃ A : Finset α, A = (B \ X) ∪ s.biUnion t := ⟨_, rfl⟩
    have hAE : (↑A : Set α) ⊆ M.E := by
      intro y hy
      rw [Finset.mem_coe, hAd, Finset.mem_union] at hy
      rcases hy with hy | hy
      · exact hB.subset_ground (Finset.mem_coe.mpr (Finset.mem_sdiff.mp hy).1)
      · obtain ⟨x, _, hyx⟩ := Finset.mem_biUnion.mp hy
        exact hT.subset_ground (Finset.mem_coe.mpr
          (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyx).1).1)
    -- closure of `B \ X`
    have hinter : M.closure (↑B \ ↑X) = ⋂ J ∈ (fun x : {e // e ∈ B \ T} => (↑B : Set α) \ {x.1}) ''
        (↑s : Set {e // e ∈ B \ T}), M.closure J := by
      rw [← hB.indep.closure_sInter_eq_biInter_closure_of_forall_subset]
      · congr 1
        ext y
        simp only [Set.mem_sInter, Set.mem_image, Finset.mem_coe, Set.mem_diff,
          Set.mem_singleton_iff, forall_exists_index, and_imp]
        constructor
        · rintro ⟨hyB, hyX⟩ J x hx rfl
          refine ⟨hyB, fun h => hyX ?_⟩
          rw [Set.mem_singleton_iff.mp h, hXd]
          exact Finset.mem_map_of_mem _ hx
        · intro h
          obtain ⟨x0, hx0⟩ := hsne
          refine ⟨(h _ x0 hx0 rfl).1, fun hyX => ?_⟩
          rw [hXd, Finset.mem_map] at hyX
          obtain ⟨x, hx, rfl⟩ := hyX
          exact (h _ x hx rfl).2 rfl
      · obtain ⟨x0, hx0⟩ := hsne
        exact ⟨_, x0, Finset.mem_coe.mpr hx0, rfl⟩
      · rintro J ⟨x, _, rfl⟩
        exact Set.diff_subset
    have hTcl : (↑T : Set α) ⊆ M.closure ↑A := by
      intro f hf
      rw [Finset.mem_coe] at hf
      by_cases hfB : f ∈ B
      · apply M.subset_closure _ hAE
        rw [Finset.mem_coe, hAd, Finset.mem_union, Finset.mem_sdiff]
        left
        refine ⟨hfB, fun hfX => ?_⟩
        rw [hXd, Finset.mem_map] at hfX
        obtain ⟨x, _, rfl⟩ := hfX
        exact (Finset.mem_sdiff.mp x.2).2 hf
      · by_cases hfN : f ∈ s.biUnion t
        · apply M.subset_closure _ hAE
          rw [Finset.mem_coe, hAd, Finset.mem_union]
          exact Or.inr hfN
        · have hfcl : f ∈ M.closure (↑B \ ↑X) := by
            rw [hinter]
            simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_image, Finset.mem_coe]
            rintro J ⟨x, hx, rfl⟩
            by_contra hcl
            have hbase := hB.exchange_base_of_notMem_closure (Finset.mem_coe.mpr
              (Finset.mem_sdiff.mp x.2).1) hcl (hT.subset_ground (Finset.mem_coe.mpr hf))
            apply hfN
            rw [Finset.mem_biUnion]
            refine ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hf, hfB⟩, ?_⟩⟩
            rw [Finset.coe_insert, Finset.coe_erase]
            exact hbase
          apply M.closure_subset_closure _ hfcl
          intro y hy
          rw [Set.mem_diff, Finset.mem_coe, Finset.mem_coe] at hy
          rw [Finset.mem_coe, hAd, Finset.mem_union, Finset.mem_sdiff]
          exact Or.inl hy
    have hspan : M.Spanning (↑A : Set α) := by
      refine ⟨?_, hAE⟩
      apply subset_antisymm (M.closure_subset_ground _)
      rw [← hT.closure_eq]
      exact M.closure_subset_closure_of_subset_closure hTcl
    obtain ⟨B', hB', hB'A⟩ := hspan.exists_isBase_subset
    have h1 : B'.ncard = (↑B : Set α).ncard := hB'.ncard_eq_ncard_of_isBase hB
    have h2 : B'.ncard ≤ (↑A : Set α).ncard := Set.ncard_le_ncard hB'A (Set.toFinite _)
    rw [Set.ncard_coe_finset] at h1 h2
    have h3 : A.card ≤ (B \ X).card + (s.biUnion t).card := by
      rw [hAd]; exact Finset.card_union_le _ _
    have h4 : (B \ X).card = B.card - X.card := Finset.card_sdiff_of_subset hXB
    have h5 : X.card ≤ B.card := Finset.card_le_card hXB
    omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  refine ⟨fun e => if h : e ∈ B \ T then f ⟨e, h⟩ else e, ?_, ?_⟩
  · intro e he
    simp only [dif_pos he]
    have := hft ⟨e, he⟩
    rw [Finset.mem_filter] at this
    exact this
  · intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    simp only [dif_pos hx, dif_pos hy] at hxy
    have := hfinj hxy
    exact congrArg Subtype.val this

theorem swap_self_eq (G : MatroidGame N E) (B : N → Finset E) (i : N) (e : E) (he : e ∈ B i) :
    G.swap B i e e = B := by
  unfold MatroidGame.swap
  rw [Finset.insert_erase he, Function.update_eq_self]

theorem mem_alts_self (G : MatroidGame N E) {B : N → Finset E} (hB : G.IsProfile B) {i : N}
    {e : E} (he : e ∈ B i) : e ∈ G.alts B i e := by
  classical
  unfold MatroidGame.alts
  rw [Finset.mem_filter, Finset.insert_erase he]
  exact ⟨Finset.mem_univ _, hB i⟩

theorem delta_ge (G : MatroidGame N E) {B : N → Finset E} (hB : G.IsProfile B) {i : N} {e : E}
    (he : e ∈ B i) (x : ℝ)
    (hx : ∀ f ∈ G.alts B i e, x ≤ G.c f (G.users f (G.swap B i e f)) + G.d i f) :
    x ≤ G.delta B i e := by
  unfold MatroidGame.delta
  rw [dif_pos ⟨e, mem_alts_self G hB he⟩]
  exact Finset.le_inf' _ _ hx

theorem delta_le (G : MatroidGame N E) {B : N → Finset E} {i : N} {e f : E}
    (hf : f ∈ G.alts B i e) :
    G.delta B i e ≤ G.c f (G.users f (G.swap B i e f)) + G.d i f := by
  unfold MatroidGame.delta
  rw [dif_pos ⟨f, hf⟩]
  exact Finset.inf'_le _ hf

theorem share_le (G : MatroidGame N E) (ξ : (N → Finset E) → N → E → ℝ)
    (hξ : G.IsSeparableProtocol ξ) {S : N → Finset E} (hS : G.IsProfile S) {i : N} {e : E}
    (hi : i ∈ G.users e S) : ξ S i e ≤ G.c e (G.users e S) := by
  rw [hξ.budget_balance S hS e ⟨i, hi⟩]
  exact Finset.single_le_sum (f := fun j => ξ S j e) (fun j _ => hξ.nonneg S hS j e) hi

theorem enf_key (G : MatroidGame N E) {B : N → Finset E} (hB : G.IsProfile B)
    (ξ : (N → Finset E) → N → E → ℝ) (hξ : G.IsSeparableProtocol ξ) (hP : G.IsPNE ξ B)
    {i : N} {e : E} (he : e ∈ B i) : ξ B i e + G.d i e ≤ G.delta B i e := by
  apply delta_ge G hB he
  intro f hf
  by_cases hfe : f = e
  · subst hfe
    rw [swap_self_eq G B i f he]
    have := share_le G ξ hξ hB ((mem_users G B f i).mpr he)
    linarith
  · have hfi := not_mem_of_alt G hB he hfe hf
    have hbase := alts_base G hf
    have hS' : G.IsProfile (G.swap B i e f) := by
      intro j
      by_cases hj : j = i
      · subst hj; rw [swap_self]; exact hbase
      · rw [swap_ne G B i e f j hj]; exact hB j
    have hpne := hP.2 i (insert f ((B i).erase e)) hbase
    have hupd : Function.update B i (insert f ((B i).erase e)) = G.swap B i e f := rfl
    rw [hupd] at hpne
    unfold MatroidGame.privCost at hpne
    rw [swap_self, Finset.sum_insert (fun h => hfi (Finset.mem_of_mem_erase h)),
      ← Finset.add_sum_erase _ _ he] at hpne
    have hsame : ∑ g ∈ (B i).erase e, (ξ (G.swap B i e f) i g + G.d i g) =
        ∑ g ∈ (B i).erase e, (ξ B i g + G.d i g) := by
      apply Finset.sum_congr rfl
      intro g hg
      have hge : g ≠ e := Finset.ne_of_mem_erase hg
      have hgB : g ∈ B i := Finset.mem_of_mem_erase hg
      have hgf : g ≠ f := fun h => hfi (h ▸ hgB)
      have hu := users_swap_other G B i e f g hge hgf
      have := hξ.separable (G.swap B i e f) B hS' hB g hu i (by
        rw [mem_users, swap_self]
        exact Finset.mem_insert_of_mem hg)
      rw [this]
    rw [hsame] at hpne
    have h1 := share_le G ξ hξ hS' (i := i) (e := f) (by
      rw [mem_users, swap_self]; exact Finset.mem_insert_self _ _)
    linarith

/-- base shares for a profile satisfying (D2) -/
noncomputable def sigma (G : MatroidGame N E) (B : N → Finset E) (i : N) (e : E) : ℝ :=
  if ∑ j ∈ G.users e B, (G.delta B j e - G.d j e) = 0 then 0 else
    G.c e (G.users e B) * (G.delta B i e - G.d i e) /
      ∑ j ∈ G.users e B, (G.delta B j e - G.d j e)

noncomputable def protF (G : MatroidGame N E) (B : N → Finset E) (e : E) (U : Finset N)
    (i : N) : ℝ :=
  if i ∈ U then
    (if U = G.users e B then sigma G B i e else
      if (U \ G.users e B).Nonempty then
        (if i ∈ U \ G.users e B then G.c e U / ((U \ G.users e B).card : ℝ) else 0)
      else G.c e U / (U.card : ℝ))
  else 0

noncomputable def prot (G : MatroidGame N E) (B : N → Finset E) :
    (N → Finset E) → N → E → ℝ :=
  fun S i e => protF G B e (G.users e S) i

section Construct

variable (G : MatroidGame N E) (B : N → Finset E)
  (hD1 : ∀ (i : N) (e : E), e ∈ B i → G.d i e ≤ G.delta B i e)
  (hD2 : ∀ e : E, (G.users e B).Nonempty →
    G.c e (G.users e B) ≤ ∑ i ∈ G.users e B, (G.delta B i e - G.d i e))

include hD1 in
theorem cap_nonneg {i : N} {e : E} (hi : i ∈ G.users e B) : 0 ≤ G.delta B i e - G.d i e := by
  have := hD1 i e ((mem_users G B e i).mp hi)
  linarith

include hD1 in
theorem sigma_nonneg {i : N} {e : E} (hi : i ∈ G.users e B) : 0 ≤ sigma G B i e := by
  unfold sigma
  split_ifs with h
  · exact le_refl _
  · have hs : 0 ≤ ∑ j ∈ G.users e B, (G.delta B j e - G.d j e) :=
      Finset.sum_nonneg (fun j hj => cap_nonneg G B hD1 hj)
    apply div_nonneg
    · exact mul_nonneg (G.c_nonneg _ _) (cap_nonneg G B hD1 hi)
    · exact hs

include hD1 hD2 in
theorem sigma_le {i : N} {e : E} (hi : i ∈ G.users e B) :
    sigma G B i e ≤ G.delta B i e - G.d i e := by
  unfold sigma
  have hs : 0 ≤ ∑ j ∈ G.users e B, (G.delta B j e - G.d j e) :=
    Finset.sum_nonneg (fun j hj => cap_nonneg G B hD1 hj)
  split_ifs with h
  · exact cap_nonneg G B hD1 hi
  · have hpos : 0 < ∑ j ∈ G.users e B, (G.delta B j e - G.d j e) := lt_of_le_of_ne hs (Ne.symm h)
    rw [div_le_iff₀ hpos]
    have h2 := hD2 e ⟨i, hi⟩
    have h3 := cap_nonneg G B hD1 hi
    nlinarith

include hD1 hD2 in
theorem sigma_sum {e : E} (hne : (G.users e B).Nonempty) :
    ∑ i ∈ G.users e B, sigma G B i e = G.c e (G.users e B) := by
  have hs : 0 ≤ ∑ j ∈ G.users e B, (G.delta B j e - G.d j e) :=
    Finset.sum_nonneg (fun j hj => cap_nonneg G B hD1 hj)
  by_cases h : ∑ j ∈ G.users e B, (G.delta B j e - G.d j e) = 0
  · have : G.c e (G.users e B) = 0 := by
      have := hD2 e hne
      have := G.c_nonneg e (G.users e B)
      linarith
    rw [this]
    apply Finset.sum_eq_zero
    intro i _
    unfold sigma
    rw [if_pos h]
  · unfold sigma
    simp only [if_neg h]
    rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc, div_self h, mul_one]


theorem users_update_old (G : MatroidGame N E) (B : N → Finset E) (i : N) (T : Finset E)
    (g : E) (hgT : g ∈ T) (hgB : g ∈ B i) :
    G.users g (Function.update B i T) = G.users g B := by
  ext j
  rw [mem_users, mem_users]
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    exact ⟨fun _ => hgB, fun _ => hgT⟩
  · rw [Function.update_of_ne hj]

theorem users_update_new (G : MatroidGame N E) (B : N → Finset E) (i : N) (T : Finset E)
    (g : E) (hgT : g ∈ T) (hgB : g ∉ B i) :
    G.users g (Function.update B i T) = insert i (G.users g B) := by
  ext j
  rw [mem_users, Finset.mem_insert, mem_users]
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    exact ⟨fun _ => Or.inl rfl, fun _ => hgT⟩
  · rw [Function.update_of_ne hj]
    exact ⟨fun h => Or.inr h, fun h => h.resolve_left hj⟩

include hD1 hD2 in
theorem prot_pne (hB : G.IsProfile B) : G.IsPNE (prot G B) B := by
  classical
  refine ⟨hB, fun i T hT => ?_⟩
  unfold MatroidGame.privCost
  obtain ⟨φ, hφ, hinj⟩ := base_matching (G.M i) (B i) T (hB i) hT
  have hold : ∀ g ∈ B i, prot G B B i g = sigma G B i g := by
    intro g hg
    unfold prot protF
    rw [if_pos ((mem_users G B g i).mpr hg), if_pos rfl]
  have hold' : ∀ g ∈ T ∩ B i, prot G B (Function.update B i T) i g = sigma G B i g := by
    intro g hg
    rw [Finset.mem_inter] at hg
    unfold prot
    rw [users_update_old G B i T g hg.1 hg.2]
    unfold protF
    rw [if_pos ((mem_users G B g i).mpr hg.2), if_pos rfl]
  have hnew : ∀ g ∈ T \ B i, prot G B (Function.update B i T) i g =
      G.c g (insert i (G.users g B)) := by
    intro g hg
    rw [Finset.mem_sdiff] at hg
    have hiU : i ∉ G.users g B := by rw [mem_users]; exact hg.2
    unfold prot
    rw [users_update_new G B i T g hg.1 hg.2]
    unfold protF
    have hne : insert i (G.users g B) ≠ G.users g B := by
      intro h
      apply hiU
      rw [← h]
      exact Finset.mem_insert_self _ _
    have hdiff : insert i (G.users g B) \ G.users g B = {i} := by
      ext j
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact h1
        · exact absurd h1 h2
      · rintro rfl
        exact ⟨Or.inl rfl, hiU⟩
    rw [if_pos (Finset.mem_insert_self _ _), if_neg hne, hdiff, if_pos (Finset.singleton_nonempty _),
      if_pos (Finset.mem_singleton_self _), Finset.card_singleton, Nat.cast_one, div_one]
  -- split both costs
  rw [Function.update_self, ← Finset.sum_inter_add_sum_sdiff (B i) T,
    ← Finset.sum_inter_add_sum_sdiff T (B i)]
  have e1 : ∑ x ∈ B i ∩ T, (prot G B B i x + G.d i x) =
      ∑ x ∈ T ∩ B i, (prot G B (Function.update B i T) i x + G.d i x) := by
    rw [Finset.inter_comm]
    apply Finset.sum_congr rfl
    intro g hg
    rw [hold' g hg, hold g (Finset.mem_inter.mp hg).2]
  have e2 : ∑ x ∈ T \ B i, (prot G B (Function.update B i T) i x + G.d i x) =
      ∑ x ∈ T \ B i, (G.c x (insert i (G.users x B)) + G.d i x) :=
    Finset.sum_congr rfl (fun g hg => by rw [hnew g hg])
  rw [e1, e2]
  have key : ∑ x ∈ B i \ T, (prot G B B i x + G.d i x) ≤
      ∑ x ∈ T \ B i, (G.c x (insert i (G.users x B)) + G.d i x) := by
    calc ∑ x ∈ B i \ T, (prot G B B i x + G.d i x)
        ≤ ∑ x ∈ B i \ T, (G.c (φ x) (insert i (G.users (φ x) B)) + G.d i (φ x)) := by
          apply Finset.sum_le_sum
          intro x hx
          obtain ⟨hφT, hφb⟩ := hφ x hx
          have hxB : x ∈ B i := (Finset.mem_sdiff.mp hx).1
          have hφB : φ x ∉ B i := (Finset.mem_sdiff.mp hφT).2
          rw [hold x hxB]
          have h1 := sigma_le G B hD1 hD2 ((mem_users G B x i).mpr hxB)
          have halt : φ x ∈ G.alts B i x := by
            unfold MatroidGame.alts
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hφb⟩
          have h2 := delta_le G halt
          rw [users_swap_f G B i x (φ x)] at h2
          linarith
      _ = ∑ y ∈ (B i \ T).image φ, (G.c y (insert i (G.users y B)) + G.d i y) :=
          (Finset.sum_image (f := fun y => G.c y (insert i (G.users y B)) + G.d i y) hinj).symm
      _ ≤ ∑ x ∈ T \ B i, (G.c x (insert i (G.users x B)) + G.d i x) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro y hy
            rw [Finset.mem_image] at hy
            obtain ⟨x, hx, rfl⟩ := hy
            exact (hφ x hx).1
          · intro y _ _
            exact add_nonneg (G.c_nonneg _ _) (G.d_nonneg _ _)
  linarith

include hD1 hD2 in
theorem prot_sep (hB : G.IsProfile B) : G.IsSeparableProtocol (prot G B) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S _ i e
    unfold prot protF
    split_ifs with h1 h2 h3 h4
    · rw [h2] at h1; exact sigma_nonneg G B hD1 h1
    · exact div_nonneg (G.c_nonneg _ _) (Nat.cast_nonneg _)
    · exact le_refl _
    · exact div_nonneg (G.c_nonneg _ _) (Nat.cast_nonneg _)
    · exact le_refl _
  · exact ⟨B, prot_pne G B hD1 hD2 hB⟩
  · intro S _ e hne
    unfold prot
    by_cases hU : G.users e S = G.users e B
    · rw [hU]
      have := sigma_sum G B hD1 hD2 (hU ▸ hne)
      rw [← this]
      apply Finset.sum_congr rfl
      intro i hi
      unfold protF
      rw [if_pos hi, if_pos rfl]
    · by_cases hN : (G.users e S \ G.users e B).Nonempty
      · have hcard : (0 : ℝ) < ((G.users e S \ G.users e B).card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr hN
        have : ∑ i ∈ G.users e S, protF G B e (G.users e S) i =
            ∑ i ∈ G.users e S \ G.users e B,
              G.c e (G.users e S) / ((G.users e S \ G.users e B).card : ℝ) := by
          rw [← Finset.sum_subset Finset.sdiff_subset]
          · apply Finset.sum_congr rfl
            intro i hi
            unfold protF
            rw [if_pos (Finset.mem_sdiff.mp hi).1, if_neg hU, if_pos hN, if_pos hi]
          · intro i hi hni
            unfold protF
            rw [if_pos hi, if_neg hU, if_pos hN, if_neg hni]
        rw [this, Finset.sum_const, nsmul_eq_mul]
        field_simp
      · have hcard : (0 : ℝ) < ((G.users e S).card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr hne
        have : ∑ i ∈ G.users e S, protF G B e (G.users e S) i =
            ∑ i ∈ G.users e S, G.c e (G.users e S) / ((G.users e S).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          unfold protF
          rw [if_pos hi, if_neg hU, if_neg hN]
        rw [this, Finset.sum_const, nsmul_eq_mul]
        field_simp
  · intro S _ e i hi
    unfold prot protF
    rw [if_neg hi]
  · intro S S' _ _ e hU i _
    unfold prot
    rw [hU]

end Construct


end Aux_SepCostShare_stopped_enforceable


open SepCostShare Aux_SepCostShare_stopped_enforceable in
theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E]
    [DecidableEq E] (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E)
    (hB : G.IsProfile B) :
    (∀ (i : N) (e : E), 0 ≤ G.deltaBar B i e ∧ G.deltaBar B i e ≤ G.delta B i e) ∧
      (G.Stopped B → G.Enforceable B) := by
  have hbar : ∀ (i : N) (e : E), 0 ≤ G.deltaBar B i e ∧ G.deltaBar B i e ≤ G.delta B i e := by
    intro i e
    unfold MatroidGame.deltaBar MatroidGame.delta
    by_cases h : (G.alts B i e).Nonempty
    · rw [dif_pos h, dif_pos h]
      refine ⟨Finset.le_inf' _ _ (fun f _ => add_nonneg (G.c_nonneg _ _) (G.d_nonneg _ _)), ?_⟩
      apply Finset.le_inf'
      intro f hf
      have h1 : (G.alts B i e).inf' h (fun f => G.pi i f) ≤ G.pi i f := Finset.inf'_le _ hf
      have h2 : G.c f {i} ≤ G.c f (G.users f (G.swap B i e f)) := by
        apply hG.1
        intro j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        rw [mem_users, swap_self]
        exact Finset.mem_insert_self _ _
      have h3 : G.pi i f = G.c f {i} + G.d i f := rfl
      linarith
    · rw [dif_neg h, dif_neg h]
      exact ⟨le_refl _, le_refl _⟩
  refine ⟨hbar, fun hst => ?_⟩
  have hD1 : ∀ (i : N) (e : E), e ∈ B i → G.d i e ≤ G.delta B i e := by
    intro i e he
    have h1 := (hst e).1
    unfold MatroidGame.cond1 at h1
    push_neg at h1
    have := h1 i ((mem_users G B e i).mpr he)
    have := (hbar i e).2
    linarith
  have hD2 : ∀ e : E, (G.users e B).Nonempty →
      G.c e (G.users e B) ≤ ∑ i ∈ G.users e B, (G.delta B i e - G.d i e) := by
    intro e hne
    have h2 := (hst e).2
    unfold MatroidGame.cond2 at h2
    push_neg at h2
    have h3 := h2 hne
    have h4 : ∑ i ∈ G.users e B, (G.deltaBar B i e - G.d i e) ≤
        ∑ i ∈ G.users e B, (G.delta B i e - G.d i e) :=
      Finset.sum_le_sum (fun i _ => by have := (hbar i e).2; linarith)
    linarith
  exact ⟨prot G B, prot_sep G B hD1 hD2 hB, prot_pne G B hD1 hD2 hB⟩
