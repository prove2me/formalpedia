-- Prove2me | solution 1 for SecretaryWD.Graphic.graphic_three_partition_property
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:52:52.24223+00:00
-- url     : https://prove2.me/submissions/8a13dced-9db1-445b-8cf7-d8c697986578

import Mathlib
import Definitions.Def_SecretaryWD_Graphic_GraphicMatroid
import Definitions.Def_SecretaryWD_Graphic_RandomPartition



namespace SecretaryWD.Graphic

section RP


open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def RPInv (E : Finset (Sym2 V)) (P : Finset (Finset (Sym2 V))) : Prop :=
  IsPartitionOf E P ∧ ∀ S : Finset (Sym2 V), IsPartIndep P S → IsAcyclicSet S

lemma rp_edge_eq {e : Sym2 V} {x x' : V} (hx : x ∈ e) (hx' : x' ∈ e) (hne : x ≠ x') :
    e = s(x, x') := by
  exact (Sym2.mem_and_mem_iff hne).1 ⟨hx, hx'⟩

lemma rp_mem_redPart {E : Finset (Sym2 V)} {col : V → Bool} {x : V} {f : Sym2 V} :
    f ∈ redPart E col x ↔ f ∈ E ∧ x ∈ f ∧ ∃ y ∈ f, col y = false := by
  unfold redPart; simp [Finset.mem_filter]

lemma rp_mem_roundParts {E : Finset (Sym2 V)} {col : V → Bool} {p : Finset (Sym2 V)} :
    p ∈ roundParts E col ↔ (∃ x, col x = true ∧ redPart E col x = p) ∧ p.Nonempty := by
  unfold roundParts; simp [Finset.mem_filter, Finset.mem_image]

lemma rp_mem_blue {E : Finset (Sym2 V)} {col : V → Bool} {f : Sym2 V} :
    f ∈ blueEdges E col ↔ f ∈ E ∧ ∀ y ∈ f, col y = false := by
  unfold blueEdges; simp [Finset.mem_filter]

/-- An edge in some round part, containing a red node `x`, lies in `redPart x`. -/
lemma rp_in_redPart_of {E : Finset (Sym2 V)} {col : V → Bool} {x x' : V} {f : Sym2 V}
    (hx : col x = true) (hxf : x ∈ f) (hf : f ∈ redPart E col x') (hx' : col x' = true) :
    f ∈ redPart E col x := by
  rw [rp_mem_redPart] at hf ⊢
  obtain ⟨hfE, hx'f, y, hy, hcy⟩ := hf
  refine ⟨hfE, hxf, y, hy, hcy⟩

lemma rp_red_eq {E : Finset (Sym2 V)} {col : V → Bool} {x x' : V} {f : Sym2 V}
    (hx : col x = true) (hxf : x ∈ f) (hf : f ∈ redPart E col x') (hx' : col x' = true) :
    x = x' := by
  by_contra hne
  rw [rp_mem_redPart] at hf
  obtain ⟨_, hx'f, y, hy, hcy⟩ := hf
  have := rp_edge_eq hxf hx'f hne
  subst this
  rcases Sym2.mem_iff.1 hy with rfl | rfl <;> simp_all

lemma rp_step (E : Finset (Sym2 V)) (col : V → Bool) (Q : Finset (Finset (Sym2 V)))
    (hQ : RPInv (blueEdges E col) Q) : RPInv E (roundParts E col ∪ Q) := by
  obtain ⟨⟨hQa, hQb⟩, hQc⟩ := hQ
  have hblueE : blueEdges E col ⊆ E := fun f hf => (rp_mem_blue.1 hf).1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨⟨x, hx, rfl⟩, hne⟩ := rp_mem_roundParts.1 hp
      exact ⟨hne, fun f hf => (rp_mem_redPart.1 hf).1⟩
    · exact ⟨(hQa p hp).1, (hQa p hp).2.trans hblueE⟩
  · intro p hp p' hp' hpp'
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hp hp'
    -- generic disjointness via elements
    have key : ∀ p ∈ roundParts E col, ∀ p' ∈ roundParts E col ∪ Q, p ≠ p' →
        Disjoint p p' := by
      intro p hp p' hp' hpp'
      obtain ⟨⟨x, hx, rfl⟩, _⟩ := rp_mem_roundParts.1 hp
      rw [Finset.disjoint_left]
      intro f hf hf'
      have hxf := (rp_mem_redPart.1 hf).2.1
      rcases Finset.mem_union.1 hp' with hp' | hp'
      · obtain ⟨⟨x', hx', rfl⟩, _⟩ := rp_mem_roundParts.1 hp'
        exact hpp' (by rw [rp_red_eq hx hxf hf' hx'])
      · have := (rp_mem_blue.1 ((hQa p' hp').2 hf')).2 x hxf
        simp_all
    rcases hp with hp | hp
    · exact key p hp p' (by simp_all) hpp'
    rcases hp' with hp' | hp'
    · exact (key p' hp' p (by simp_all) (Ne.symm hpp')).symm
    · exact hQb hp hp' hpp'
  · intro S ⟨hS1, hS2⟩
    set S2 := S.filter (fun e => ∃ q ∈ Q, e ∈ q) with hS2def
    have hS2ind : IsPartIndep Q S2 := by
      refine ⟨fun e he => (Finset.mem_filter.1 he).2, fun q hq => ?_⟩
      refine le_trans (Finset.card_le_card ?_) (hS2 q (Finset.mem_union_right _ hq))
      exact Finset.inter_subset_inter_right (Finset.filter_subset _ _)
    have hS2ac := hQc S2 hS2ind
    intro u c hc
    by_cases hall : ∀ e ∈ c.edges, e ∈ (SimpleGraph.fromEdgeSet (S2 : Set (Sym2 V))).edgeSet
    · exact hS2ac _ (hc.transfer hall)
    push_neg at hall
    obtain ⟨e, hec, heS2⟩ := hall
    have heS : e ∈ (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).edgeSet := c.edges_subset_edgeSet hec
    rw [SimpleGraph.edgeSet_fromEdgeSet] at heS
    have heS' : e ∈ S := heS.1
    have heS2' : e ∉ S2 := by
      intro h; apply heS2; rw [SimpleGraph.edgeSet_fromEdgeSet]; exact ⟨h, heS.2⟩
    obtain ⟨p, hp, hep⟩ := hS1 e heS'
    have hpR : p ∈ roundParts E col := by
      rcases Finset.mem_union.1 hp with hp | hp
      · exact hp
      · exact absurd (Finset.mem_filter.2 ⟨heS', p, hp, hep⟩) heS2'
    obtain ⟨⟨x, hx, rfl⟩, hpne⟩ := rp_mem_roundParts.1 hpR
    have hxe : x ∈ e := (rp_mem_redPart.1 hep).2.1
    -- every S-edge containing x lies in redPart x
    have hinc : ∀ f ∈ S, x ∈ f → f ∈ redPart E col x := by
      intro f hfS hxf
      obtain ⟨p', hp', hfp'⟩ := hS1 f hfS
      rcases Finset.mem_union.1 hp' with hp' | hp'
      · obtain ⟨⟨x', hx', rfl⟩, _⟩ := rp_mem_roundParts.1 hp'
        exact rp_in_redPart_of hx hxf hfp' hx'
      · have := (rp_mem_blue.1 ((hQa p' hp').2 hfp')).2 x hxf
        simp_all
    have hcard := hS2 _ hp
    -- rotate cycle to start at x
    have hxs : x ∈ c.support := by
      induction e using Sym2.ind with
      | h a b =>
        rcases Sym2.mem_iff.1 hxe with rfl | rfl
        · exact c.fst_mem_support_of_mem_edges hec
        · exact c.snd_mem_support_of_mem_edges hec
    have hc' := hc.rotate hxs
    generalize c.rotate x hxs = d at hc'
    cases d with
    | nil => exact hc'.not_of_nil
    | cons h p =>
      rename_i y
      rw [SimpleGraph.Walk.cons_isCycle_iff] at hc'
      obtain ⟨hpath, hnot⟩ := hc'
      -- last edge of p contains x
      have hyx : y ≠ x := (h.ne).symm
      obtain ⟨f, hfp, hxf⟩ : ∃ f ∈ p.edges, x ∈ f := by
        cases hr : p.reverse with
        | nil => exact absurd rfl hyx
        | cons h' q =>
          rename_i z
          refine ⟨s(x, z), ?_, Sym2.mem_mk_left _ _⟩
          have : s(x, z) ∈ p.reverse.edges := by rw [hr]; simp
          simpa using this
      have hfS : f ∈ S := by
        have := p.edges_subset_edgeSet hfp
        rw [SimpleGraph.edgeSet_fromEdgeSet] at this
        exact this.1
      have h0S : s(x, y) ∈ S := by
        have := h
        rw [SimpleGraph.fromEdgeSet_adj] at this
        exact this.1
      have hfne : f ≠ s(x, y) := fun h => hnot (h ▸ hfp)
      apply hfne
      have h1 : f ∈ S ∩ redPart E col x := Finset.mem_inter.2 ⟨hfS, hinc f hfS hxf⟩
      have h2 : s(x, y) ∈ S ∩ redPart E col x :=
        Finset.mem_inter.2 ⟨h0S, hinc _ h0S (Sym2.mem_mk_left _ _)⟩
      exact Finset.card_le_one.1 hcard _ h1 _ h2

lemma rp_main : ∀ (n : ℕ) (E : Finset (Sym2 V)), E.card = n →
    ∀ P ∈ (partitionPMF E).support, RPInv E P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hE P hP
  rw [partitionPMF] at hP
  split_ifs at hP with h
  · simp only [PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hP
    obtain ⟨e, _, b, _, c, _, Q, hQ, rfl⟩ := hP
    apply rp_step
    exact ih _ (hE ▸ blueEdges_card_lt E e b c) _ rfl Q hQ
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hP
    subst hP
    refine ⟨⟨by simp, by simp⟩, fun S hS => ?_⟩
    have : S = ∅ := by
      ext e; simp only [Finset.notMem_empty, iff_false]
      intro he; obtain ⟨p, hp, _⟩ := hS.1 e he; simp at hp
    subst this; exact isAcyclicSet_empty

theorem random_partition_indep_acyclic_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ P ∈ (partitionPMF G.edgeFinset).support,
      IsPartitionOf G.edgeFinset P ∧
        ∀ S : Finset (Sym2 V), IsPartIndep P S → IsAcyclicSet S :=
  rp_main _ _ rfl


end RP

section FO


open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma acyc_unique_parent {H : SimpleGraph V} (hH : H.IsAcyclic) {r x y z : V}
    (hy : H.Adj x y) (hz : H.Adj x z) (hr : H.Reachable r x)
    (hdy : H.dist r x = H.dist r y + 1) (hdz : H.dist r x = H.dist r z + 1) : y = z := by
  have hry : H.Reachable r y := hr.trans hy.reachable
  have hrz : H.Reachable r z := hr.trans hz.reachable
  obtain ⟨q, hq, hql⟩ := hr.exists_path_of_dist
  obtain ⟨py, hpy, hpyl⟩ := hry.exists_path_of_dist
  obtain ⟨pz, hpz, hpzl⟩ := hrz.exists_path_of_dist
  have notin : ∀ {w : V} (p : H.Walk r w), p.length = H.dist r w → H.dist r x = H.dist r w + 1 →
      x ∉ p.support := by
    intro w p hpl hd hx
    have h1 := SimpleGraph.dist_le (p.takeUntil x hx)
    have h2 := p.length_takeUntil_le hx
    omega
  have hyq : y ∈ q.support :=
    hH.mem_support_of_ne_mem_support_of_adj_of_isPath hq hpy hy (notin py hpyl hdy)
  have hzq : z ∈ q.support :=
    hH.mem_support_of_ne_mem_support_of_adj_of_isPath hq hpz hz (notin pz hpzl hdz)
  have e1 := hH.path_concat hpy hq hy.symm hyq
  have e2 := hH.path_concat hpz hq hz.symm hzq
  have := congrArg (fun w => w.reverse.snd) (e1.symm.trans e2)
  simpa [SimpleGraph.Walk.reverse_concat] using this

lemma forest_orient (S : Finset (Sym2 V)) (hS : IsAcyclicSet S) (hloop : ∀ f ∈ S, ¬ f.IsDiag)
    (v : Sym2 V → ℝ) :
    ∃ C : Finset (V × V), (∀ c ∈ C, s(c.1, c.2) ∈ S ∧ c.1 ≠ c.2) ∧
      (∀ c ∈ C, ∀ c' ∈ C, c.1 = c'.1 → c = c') ∧
      ∑ c ∈ C, v s(c.1, c.2) = ∑ f ∈ S, v f := by
  set H := SimpleGraph.fromEdgeSet (S : Set (Sym2 V)) with hHdef
  have hH : H.IsAcyclic := hS
  let rt : V → V := fun z => Quot.out (H.connectedComponentMk z)
  have hrt : ∀ z, H.Reachable (rt z) z := by
    intro z
    apply SimpleGraph.ConnectedComponent.exact
    exact Quot.out_eq _
  have hrt_adj : ∀ a b, H.Adj a b → rt a = rt b := by
    intro a b h
    simp only [rt]
    rw [SimpleGraph.ConnectedComponent.sound h.reachable]
  let φ : Sym2 V → V × V := fun f =>
    if H.dist (rt f.out.1) f.out.2 < H.dist (rt f.out.1) f.out.1 then (f.out.1, f.out.2)
    else (f.out.2, f.out.1)
  have hφs : ∀ f, s((φ f).1, (φ f).2) = f := by
    intro f
    simp only [φ]
    split_ifs
    · exact Quot.out_eq f
    · rw [Sym2.eq_swap]; exact Quot.out_eq f
  have hφprop : ∀ f ∈ S, H.Adj (φ f).1 (φ f).2 ∧
      H.dist (rt (φ f).1) (φ f).1 = H.dist (rt (φ f).1) (φ f).2 + 1 := by
    intro f hf
    have hadj : H.Adj f.out.1 f.out.2 := by
      rw [hHdef, SimpleGraph.fromEdgeSet_adj]
      refine ⟨by rw [show s(f.out.1, f.out.2) = f from Quot.out_eq f]; exact Finset.mem_coe.2 hf, ?_⟩
      intro h
      apply hloop f hf
      rw [← Quot.out_eq f]
      exact Sym2.mk_isDiag_iff.2 h
    have hreach := hrt f.out.1
    have hor := hH.dist_eq_dist_add_one_of_adj_of_reachable (rt f.out.1) hadj hreach
    simp only [φ]
    split_ifs with hlt
    · refine ⟨hadj, ?_⟩
      dsimp only
      omega
    · refine ⟨hadj.symm, ?_⟩
      dsimp only
      rw [← hrt_adj _ _ hadj]
      omega
  refine ⟨S.image φ, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨by rw [hφs]; exact hf, (hφprop f hf).1.ne⟩
  · intro c hc c' hc' h1
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hc'
    obtain ⟨ha, hd⟩ := hφprop f hf
    obtain ⟨ha', hd'⟩ := hφprop f' hf'
    rw [← h1] at ha' hd'
    have := acyc_unique_parent hH ha ha' (hrt _) hd hd'
    exact Prod.ext h1 this
  · rw [Finset.sum_image]
    · exact Finset.sum_congr rfl (fun f _ => by rw [hφs])
    · intro f _ f' _ h
      rw [← hφs f, ← hφs f', h]


end FO

section PM


open Classical

lemma pmfExp_bind' {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (g : α → PMF β)
    (f : β → ℝ) : pmfExp (p.bind g) f = pmfExp p (fun a => pmfExp (g a) f) := by
  unfold pmfExp
  simp_rw [PMF.bind_apply, tsum_fintype]
  simp_rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (PMF.apply_ne_top _ _)), ENNReal.toReal_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring

lemma pmfExp_pure' {α : Type*} [Fintype α] (a : α) (f : α → ℝ) :
    pmfExp (PMF.pure a) f = f a := by
  unfold pmfExp
  simp only [PMF.pure_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma pmfExp_map' {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (h : α → β)
    (f : β → ℝ) : pmfExp (p.map h) f = pmfExp p (fun a => f (h a)) := by
  rw [← PMF.bind_pure_comp, pmfExp_bind']
  simp [Function.comp, pmfExp_pure']

lemma pmfExp_const' {α : Type*} [Fintype α] (p : PMF α) (K : ℝ) :
    pmfExp p (fun _ => K) = K := by
  unfold pmfExp
  rw [← Finset.sum_mul]
  have : ∑ a, (p a).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top _ _)]
    have := p.tsum_coe
    rw [tsum_fintype] at this
    rw [this]; simp
  rw [this, one_mul]

lemma pmfExp_add' {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfExp p (fun a => f a + g a) = pmfExp p f + pmfExp p g := by
  unfold pmfExp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

lemma pmfExp_sum' {α ι : Type*} [Fintype α] (p : PMF α) (s : Finset ι) (f : ι → α → ℝ) :
    pmfExp p (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, pmfExp p (f i) := by
  unfold pmfExp
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma pmfExp_mul' {α : Type*} [Fintype α] (μ : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfExp μ (fun a => c * f a) = c * pmfExp μ f := by
  unfold pmfExp; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring

lemma pmfExp_mono' {α : Type*} [Fintype α] (μ : PMF α) (f g : α → ℝ)
    (h : ∀ a ∈ μ.support, f a ≤ g a) : pmfExp μ f ≤ pmfExp μ g := by
  unfold pmfExp
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a ∈ μ.support
  · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

lemma pmfExp_uniform' {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    pmfExp (PMF.uniformOfFintype α) f = (1 / (Fintype.card α : ℝ)) * ∑ a, f a := by
  unfold pmfExp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  simp [PMF.uniformOfFintype_apply, ENNReal.toReal_inv]

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def flipAt (x : V) : Equiv.Perm (V → Bool) :=
  Function.Involutive.toPerm (fun c => Function.update c x (!c x)) (by
    intro c; ext z; by_cases h : z = x <;> simp [Function.update, h])

lemma flipAt_apply_self (x : V) (c : V → Bool) : flipAt x c x = !c x := by
  show Function.update c x (!c x) x = !c x
  simp

lemma flipAt_apply_ne (x : V) (c : V → Bool) (z : V) (h : z ≠ x) : flipAt x c z = c z := by
  show Function.update c x (!c x) z = c z
  simp [h]

lemma sum_one_var (y : V) (F : Bool → ℝ) :
    ∑ c : V → Bool, F (c y) = (Fintype.card (V → Bool) : ℝ) / 2 * (F true + F false) := by
  have h1 : ∑ c : V → Bool, F (c y) = ∑ c : V → Bool, F (!c y) := by
    rw [← Equiv.sum_comp (flipAt y)]
    simp [flipAt_apply_self]
  have h2 : ∑ c : V → Bool, (F (c y) + F (!c y)) = ∑ _c : V → Bool, (F true + F false) := by
    apply Finset.sum_congr rfl; intro c _; cases c y <;> simp [add_comm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← h1] at h2
  linarith

lemma sum_two_var (x y : V) (hxy : x ≠ y) (F : Bool → Bool → ℝ) :
    ∑ c : V → Bool, F (c x) (c y) = (Fintype.card (V → Bool) : ℝ) / 4 *
      (F true true + F true false + F false true + F false false) := by
  have hx : ∀ G : (V → Bool) → ℝ, ∑ c, G c = ∑ c, G (flipAt x c) :=
    fun G => (Equiv.sum_comp (flipAt x) G).symm
  have hy : ∀ G : (V → Bool) → ℝ, ∑ c, G c = ∑ c, G (flipAt y c) :=
    fun G => (Equiv.sum_comp (flipAt y) G).symm
  have e1 : ∑ c : V → Bool, F (c x) (c y) = ∑ c : V → Bool, F (!c x) (c y) := by
    rw [hx]; simp [flipAt_apply_self, flipAt_apply_ne x _ y (Ne.symm hxy)]
  have e2 : ∑ c : V → Bool, F (c x) (c y) = ∑ c : V → Bool, F (c x) (!c y) := by
    rw [hy]; simp [flipAt_apply_self, flipAt_apply_ne y _ x hxy]
  have e3 : ∑ c : V → Bool, F (c x) (c y) = ∑ c : V → Bool, F (!c x) (!c y) := by
    rw [e1, hy]; simp [flipAt_apply_self, flipAt_apply_ne y _ x hxy]
  have h4 : ∑ c : V → Bool, (F (c x) (c y) + F (!c x) (c y) + F (c x) (!c y) + F (!c x) (!c y))
      = ∑ _c : V → Bool, (F true true + F true false + F false true + F false false) := by
    apply Finset.sum_congr rfl; intro c _
    cases c x <;> cases c y <;> simp <;> ring
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h4
  rw [← e1, ← e2, ← e3] at h4
  linarith

/-- the weight -/
noncomputable def wt (a b : Bool) : ℝ :=
  if a = true ∧ b = false then 1 else if a = false ∧ b = false then 1 / 3 else 0

lemma wt_nonneg (a b : Bool) : 0 ≤ wt a b := by
  unfold wt; split_ifs <;> norm_num

lemma caseA (x y : V) (hxy : x ≠ y) :
    ∑ c : V → Bool, wt (c x) (c y) = (Fintype.card (V → Bool) : ℝ) / 3 := by
  rw [sum_two_var x y hxy]; simp [wt]; ring

lemma caseB (y : V) (a : Bool) :
    ∑ c : V → Bool, wt a (c y) = (Fintype.card (V → Bool) : ℝ) / 2 * (wt a true + wt a false) :=
  sum_one_var y (wt a)

lemma caseC (x : V) (b : Bool) :
    ∑ c : V → Bool, wt (c x) b = (Fintype.card (V → Bool) : ℝ) / 2 * (wt true b + wt false b) :=
  sum_one_var x (fun a => wt a b)

lemma round_prob (e : Sym2 V) (he : ¬ e.IsDiag) (x y : V) (hxy : x ≠ y) :
    1 / 3 ≤ pmfExp (PMF.uniformOfFintype Bool) (fun b =>
      pmfExp (PMF.uniformOfFintype (V → Bool)) (fun c =>
        wt (roundColoring e b c x) (roundColoring e b c y))) := by
  have hne : e.out.1 ≠ e.out.2 := by
    intro h; apply he; rw [← Quot.out_eq e]; exact (Sym2.mk_isDiag_iff).2 h
  have hN : (0 : ℝ) < Fintype.card (V → Bool) := by exact_mod_cast Fintype.card_pos
  simp only [pmfExp_uniform', Fintype.card_bool, Fintype.sum_bool]
  have rc : ∀ b c z, roundColoring e b c z =
      if z = e.out.1 then b else if z = e.out.2 then !b else c z := fun _ _ _ => rfl
  simp only [rc]
  generalize e.out.1 = u at hne ⊢
  generalize e.out.2 = w at hne ⊢
  by_cases hxu : x = u <;> by_cases hxw : x = w <;> by_cases hyu : y = u <;>
    by_cases hyw : y = w
  all_goals (try subst hxu)
  all_goals (try subst hxw)
  all_goals (try subst hyu)
  all_goals (try subst hyw)
  all_goals (try (exact absurd rfl hne))
  all_goals (try (exact absurd rfl hxy))
  all_goals simp only [if_true, if_false, Bool.not_true, Bool.not_false, ite_true, ite_false,
    ne_eq, not_false_eq_true, *]
  all_goals (try simp only [caseA x y hxy, caseB, caseC, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul])
  all_goals (try simp only [wt])
  all_goals (try norm_num)
  all_goals (try field_simp)
  all_goals (try norm_num)


end PM

section TP
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def ValidC (E : Finset (Sym2 V)) (C : Finset (V × V)) : Prop :=
  (∀ c ∈ C, s(c.1, c.2) ∈ E ∧ c.1 ≠ c.2) ∧ (∀ c ∈ C, ∀ c' ∈ C, c.1 = c'.1 → c = c')

lemma partMax_nonneg' (p : Finset (Sym2 V)) (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) :
    0 ≤ partMax p v := by
  unfold partMax
  split_ifs with h
  · obtain ⟨e, he⟩ := h
    exact (hv e).trans (Finset.le_sup' v he)
  · exact le_refl _

lemma round_lower (E : Finset (Sym2 V)) (col : V → Bool) (C : Finset (V × V)) (hC : ValidC E C)
    (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) (Q : Finset (Finset (Sym2 V)))
    (hQ : IsPartitionOf (blueEdges E col) Q) :
    ∑ c ∈ C, v s(c.1, c.2) * (if col c.1 = true ∧ col c.2 = false then 1 else 0) +
      partitionValue Q v ≤ partitionValue (roundParts E col ∪ Q) v := by
  have hdisj : Disjoint (roundParts E col) Q := by
    rw [Finset.disjoint_left]
    intro p hp hpQ
    obtain ⟨⟨x, hx, rfl⟩, ⟨f, hf⟩⟩ := rp_mem_roundParts.1 hp
    have hxf := (rp_mem_redPart.1 hf).2.1
    have := (rp_mem_blue.1 ((hQ.1 _ hpQ).2 hf)).2 x hxf
    simp_all
  unfold partitionValue
  rw [Finset.sum_union hdisj]
  refine add_le_add ?_ le_rfl
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  set CR := C.filter (fun c => col c.1 = true ∧ col c.2 = false)
  have hmem : ∀ c ∈ CR, s(c.1, c.2) ∈ redPart E col c.1 := by
    intro c hc
    have hf := Finset.mem_filter.1 hc
    rw [rp_mem_redPart]
    exact ⟨(hC.1 c hf.1).1, Sym2.mem_mk_left _ _, c.2, Sym2.mem_mk_right _ _, hf.2.2⟩
  calc ∑ c ∈ CR, v s(c.1, c.2) ≤ ∑ c ∈ CR, partMax (redPart E col c.1) v := by
        apply Finset.sum_le_sum
        intro c hc
        unfold partMax
        rw [dif_pos ⟨_, hmem c hc⟩]
        exact Finset.le_sup' v (hmem c hc)
    _ = ∑ p ∈ CR.image (fun c => redPart E col c.1), partMax p v := by
        rw [Finset.sum_image]
        intro c hc c' hc' h
        have hc1 := hmem c hc
        rw [show redPart E col c.1 = redPart E col c'.1 from h] at hc1
        have hx := (Finset.mem_filter.1 hc).2.1
        have hx' := (Finset.mem_filter.1 hc').2.1
        have := rp_red_eq hx (Sym2.mem_mk_left _ _) hc1 hx'
        exact hC.2 c (Finset.mem_filter.1 hc).1 c' (Finset.mem_filter.1 hc').1 this
    _ ≤ ∑ p ∈ roundParts E col, partMax p v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
          rw [rp_mem_roundParts]
          exact ⟨⟨c.1, (Finset.mem_filter.1 hc).2.1, rfl⟩, ⟨_, hmem c hc⟩⟩
        · intro p _ _; exact partMax_nonneg' p v hv

lemma wt_split (a b : Bool) (t : ℝ) :
    t * wt a b = t * (if a = true ∧ b = false then 1 else 0) +
      t * (if a = false ∧ b = false then 1 else 0) / 3 := by
  unfold wt
  cases a <;> cases b <;> simp <;> ring

lemma claim_main (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) : ∀ (n : ℕ) (E : Finset (Sym2 V)),
    E.card = n → ∀ C : Finset (V × V), ValidC E C →
      ∑ c ∈ C, v s(c.1, c.2) ≤ 3 * pmfExp (partitionPMF E) (fun P => partitionValue P v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hE C hC
  rw [partitionPMF]
  split_ifs with h
  · simp only [pmfExp_bind', pmfExp_map']
    -- lower bound for the innermost expectation
    have hinner : ∀ (e : {e // e ∈ properEdges E}) (b : Bool) (c : V → Bool),
        ∑ q ∈ C, v s(q.1, q.2) * wt (roundColoring e.1 b c q.1) (roundColoring e.1 b c q.2) ≤
          pmfExp (partitionPMF (blueEdges E (roundColoring e.1 b c)))
            (fun Q => partitionValue (roundParts E (roundColoring e.1 b c) ∪ Q) v) := by
      intro e b c
      set col := roundColoring e.1 b c
      set E' := blueEdges E col
      have hlt : E'.card < n := hE ▸ blueEdges_card_lt E e b c
      set CB := C.filter (fun q => col q.1 = false ∧ col q.2 = false)
      have hCB : ValidC E' CB := by
        refine ⟨fun q hq => ?_, fun q hq q' hq' h => hC.2 q (Finset.mem_filter.1 hq).1 q'
          (Finset.mem_filter.1 hq').1 h⟩
        have hf := Finset.mem_filter.1 hq
        have hqC := hf.1
        have h1 := hf.2.1
        have h2 := hf.2.2
        refine ⟨?_, (hC.1 q hqC).2⟩
        rw [rp_mem_blue]
        refine ⟨(hC.1 q hqC).1, fun y hy => ?_⟩
        rcases Sym2.mem_iff.1 hy with rfl | rfl
        · exact h1
        · exact h2
      have hIH := ih _ hlt E' rfl CB hCB
      have hmono := pmfExp_mono' (partitionPMF E')
        (fun Q => ∑ q ∈ C, v s(q.1, q.2) * (if col q.1 = true ∧ col q.2 = false then 1 else 0) +
          partitionValue Q v)
        (fun Q => partitionValue (roundParts E col ∪ Q) v)
        (fun Q hQ => round_lower E col C hC v hv Q (rp_main _ E' rfl Q hQ).1)
      rw [pmfExp_add', pmfExp_const'] at hmono
      refine le_trans (le_of_eq ?_) (le_trans (add_le_add le_rfl (by rw [← Finset.sum_div]; linarith : ∑ q ∈ CB,
        v s(q.1, q.2) / 3 ≤ pmfExp (partitionPMF E') fun P => partitionValue P v)) hmono)
      simp only [wt_split, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp
    have hbound : ∀ e : {e // e ∈ properEdges E},
        (∑ q ∈ C, v s(q.1, q.2)) / 3 ≤
        pmfExp (PMF.uniformOfFintype Bool) (fun b => pmfExp (PMF.uniformOfFintype (V → Bool))
          (fun c => pmfExp (partitionPMF (blueEdges E (roundColoring e.1 b c)))
            (fun Q => partitionValue (roundParts E (roundColoring e.1 b c) ∪ Q) v))) := by
      intro e
      have hnd : ¬ e.1.IsDiag := (Finset.mem_filter.1 e.2).2
      calc (∑ q ∈ C, v s(q.1, q.2)) / 3 = ∑ q ∈ C, v s(q.1, q.2) * (1 / 3) := by
            rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro q _; ring
        _ ≤ ∑ q ∈ C, v s(q.1, q.2) * pmfExp (PMF.uniformOfFintype Bool) (fun b =>
              pmfExp (PMF.uniformOfFintype (V → Bool)) (fun c =>
                wt (roundColoring e.1 b c q.1) (roundColoring e.1 b c q.2))) := by
            apply Finset.sum_le_sum
            intro q hq
            exact mul_le_mul_of_nonneg_left (round_prob e.1 hnd q.1 q.2 (hC.1 q hq).2) (hv _)
        _ = pmfExp (PMF.uniformOfFintype Bool) (fun b =>
              pmfExp (PMF.uniformOfFintype (V → Bool)) (fun c =>
                ∑ q ∈ C, v s(q.1, q.2) * wt (roundColoring e.1 b c q.1)
                  (roundColoring e.1 b c q.2))) := by
            simp only [pmfExp_sum', pmfExp_mul']
        _ ≤ _ := by
            apply pmfExp_mono'; intro b _
            apply pmfExp_mono'; intro c _
            exact hinner e b c
    have := pmfExp_mono' (PMF.uniformOfFinset (properEdges E).attach (by simpa using h))
      (fun _ => (∑ q ∈ C, v s(q.1, q.2)) / 3) _ (fun e _ => hbound e)
    rw [pmfExp_const'] at this
    linarith
  · have hC0 : C = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro q hq
      apply h
      refine ⟨s(q.1, q.2), ?_⟩
      simp only [properEdges, Finset.mem_filter]
      exact ⟨(hC.1 q hq).1, fun hd => (hC.1 q hq).2 (Sym2.mk_isDiag_iff.1 hd)⟩
    subst hC0
    rw [pmfExp_pure']
    simp [partitionValue]

theorem graphic_three_partition_property_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsPartitionScheme G.edgeFinset (partitionPMF G.edgeFinset) 3 := by
  refine ⟨fun P hP => rp_main _ _ rfl P hP, fun v hv => ?_⟩
  unfold OPT
  obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_sup' ⟨∅, empty_mem_acyclicSubsets G.edgeFinset⟩
    (fun S => ∑ e ∈ S, v e)
  rw [hSeq]
  unfold acyclicSubsets at hS
  obtain ⟨hSE, hSac⟩ := Finset.mem_filter.1 hS
  rw [Finset.mem_powerset] at hSE
  have hloop : ∀ f ∈ S, ¬ f.IsDiag := by
    intro f hf
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 (hSE hf))
  obtain ⟨C, hC1, hC2, hCsum⟩ := forest_orient S hSac hloop v
  rw [← hCsum]
  exact claim_main v hv _ G.edgeFinset rfl C
    ⟨fun c hc => ⟨hSE (hC1 c hc).1, (hC1 c hc).2⟩, hC2⟩

end TP

end SecretaryWD.Graphic

open SecretaryWD.Graphic


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsPartitionScheme G.edgeFinset (partitionPMF G.edgeFinset) 3 := by
  exact graphic_three_partition_property_core G
