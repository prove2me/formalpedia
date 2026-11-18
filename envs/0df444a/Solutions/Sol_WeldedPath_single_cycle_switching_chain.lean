-- Prove2me | solution 1 for WeldedPath.single_cycle_switching_chain
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T18:45:12.177964+00:00
-- url     : https://prove2.me/submissions/09618a5b-e030-4c36-8bf5-890f29a936a9

import Definitions.Def_FinitePermutationCoupling_BlockModel
import Definitions.Def_WeldedPath_successProb
import Mathlib.Tactic
import Definitions.Def_WeldedPath_bEdge
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Fin
import Theorems.Thm_WeldedPath_weld_color_class_card_bounds
import Theorems.Thm_WeldedPath_single_cycle_completion_count
import Theorems.Thm_FinitePermutationCoupling_random_order_switching

set_option autoImplicit false

-- Solutions.WeldedPathSwitchingModel
section

namespace WeldedPath.SwitchingModel

open Classical FinitePermutationCoupling
open scoped BigOperators

variable {n : ℕ}

/-- Frozen edges have singleton classes; the other classes retain their original names. -/
def block (l : ℕ) (G : WeldedInstance n) (e : G.edges) : G.edges ⊕ EdgeClass :=
  match G.bEdge l e.1 with
  | none => Sum.inl e
  | some b => Sum.inr b

def active (G : WeldedInstance n) : G.edges ⊕ EdgeClass → Prop
  | .inr (.wld _) => True
  | _ => False

theorem block_eq_iff (l : ℕ) (G : WeldedInstance n) (e f : G.edges) :
    block l G e = block l G f ↔
      G.bEdge l e.1 = G.bEdge l f.1 ∧ (G.bEdge l f.1 = none → e = f) := by
  cases he : G.bEdge l e.1 <;> cases hf : G.bEdge l f.1 <;>
    simp [block, he, hf]

theorem blockSupport_eq (l : ℕ) (G : WeldedInstance n) :
    blockSupport (block l G) = Finset.univ.filter (G.IsEdgePerm l) := by
  ext π
  simp only [blockSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    WeldedInstance.IsEdgePerm]
  exact forall_congr' fun e => block_eq_iff l G (π e) e

theorem bEdge_of_weld (l : ℕ) (G : WeldedInstance n) (e : G.edges)
    (he : e.1 ∈ G.weldEdges) : G.bEdge l e.1 = some (.wld (G.color e.1)) := by
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp he
  rw [← hp]
  rfl

theorem active_iff_weld (l : ℕ) (G : WeldedInstance n) (e : G.edges) :
    active G (block l G e) ↔ e.1 ∈ G.weldEdges := by
  rcases e with ⟨e, he⟩
  cases e with
  | tree v =>
    by_cases hc : n - l ≤ col n v ∧ col n v ≤ n + l <;>
      simp only [block, WeldedInstance.bEdge, hc, if_true, if_false, active] <;>
      simp [WeldedInstance.weldEdges]
  | weld u w =>
    have hw : Edge.weld u w ∈ G.weldEdges := by
      rcases Finset.mem_union.mp he with ht | hw
      · simp [WeldedInstance.treeEdges] at ht
      · exact hw
    simp [block, WeldedInstance.bEdge, active, hw]

theorem block_of_weld (l : ℕ) (G : WeldedInstance n) (e : G.edges)
    (he : e.1 ∈ G.weldEdges) :
    block l G e = Sum.inr (.wld (G.color e.1)) := by
  simp [block, bEdge_of_weld l G e he]

theorem blockFiber_eq_weld (l : ℕ) (G : WeldedInstance n) (e : G.edges)
    (he : e.1 ∈ G.weldEdges) :
    blockFiber (block l G) e =
      Finset.univ.filter (fun f : G.edges =>
        f.1 ∈ G.weldEdges ∧ G.color f.1 = G.color e.1) := by
  ext f
  simp only [blockFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have hf : f.1 ∈ G.weldEdges := (active_iff_weld l G f).mp
      (h ▸ (active_iff_weld l G e).mpr he)
    refine ⟨hf, ?_⟩
    rw [block_of_weld l G f hf, block_of_weld l G e he] at h
    simpa only [Sum.inr.injEq, EdgeClass.wld.injEq] using h
  · rintro ⟨hf, hc⟩
    rw [block_of_weld l G f hf, block_of_weld l G e he, hc]

theorem singleCycle_congr (G : WeldedInstance n) (f g : Equiv.Perm G.edges)
    (hfg : ∀ e : G.edges, e.1 ∈ G.weldEdges → f e = g e) :
    G.SingleCycle f ↔ G.SingleCycle g := by
  have hgraph : G.permWeldGraph f = G.permWeldGraph g := by
    unfold WeldedInstance.permWeldGraph
    congr 1
    funext a b
    apply propext
    constructor
    · rintro ⟨e, he, ha, hb⟩
      exact ⟨e, he, ha, by simpa only [hfg e he] using hb⟩
    · rintro ⟨e, he, ha, hb⟩
      exact ⟨e, he, ha, by simpa only [hfg e he] using hb⟩
  simp only [WeldedInstance.SingleCycle, hgraph]

theorem singleCycle_saturated (l : ℕ) (G : WeldedInstance n) :
    ActiveSaturated (block l G) (active G)
      ((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle) := by
  intro f hf g hg hfg
  rw [blockSupport_eq] at hf hg
  have hsc := singleCycle_congr G f g fun e he => hfg e ((active_iff_weld l G e).mpr he)
  simp only [Finset.mem_filter, hf, hg, true_and, hsc]

theorem edgeSing_nonempty (l : ℕ) (G : WeldedInstance n)
    (hS : (G.singSupport l).Nonempty) :
    ((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle).Nonempty := by
  obtain ⟨⟨τ, π⟩, h⟩ := hS
  simp only [WeldedInstance.singSupport, WeldedInstance.prodSupport,
    Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact ⟨π, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h.1.2, h.2⟩⟩

end WeldedPath.SwitchingModel

end


-- Solutions.WeldedPathWeldClassSubtype
section

namespace WeldedPath.SwitchingCards

theorem mem_weld_class {n l : ℕ} {G : WeldedInstance n} (α : Fin 3) (e : Edge) :
    e ∈ G.classEdges l (.wld α) ↔ e ∈ G.weldEdges ∧ G.color e = α := by
  cases e with
  | tree v =>
    by_cases h : n - l ≤ col n v ∧ col n v ≤ n + l <;>
      simp [WeldedInstance.classEdges, WeldedInstance.bEdge, WeldedInstance.weldEdges, h]
  | weld u w =>
    simp [WeldedInstance.classEdges, WeldedInstance.bEdge, WeldedInstance.edges,
      WeldedInstance.treeEdges, WeldedInstance.weldEdges]

theorem edge_subtype_mem_card {n : ℕ} (G : WeldedInstance n)
    (s : Finset Edge) (hs : s ⊆ G.edges) :
    (Finset.univ.filter (fun e : G.edges => e.1 ∈ s)).card = s.card := by
  classical
  refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro e _ e' _ h
    exact Subtype.ext h
  · intro e he
    refine ⟨⟨e, hs he⟩, ?_, rfl⟩
    simp [he]

theorem edge_subtype_weld_card {n l : ℕ} (G : WeldedInstance n) (α : Fin 3) :
    (Finset.univ.filter (fun e : G.edges => e.1 ∈ G.weldEdges ∧ G.color e.1 = α)).card =
      (G.classEdges l (.wld α)).card := by
  classical
  calc
    _ = (Finset.univ.filter (fun e : G.edges => e.1 ∈ G.classEdges l (.wld α))).card := by
      congr 1
      ext e
      simp [mem_weld_class]
    _ = _ := edge_subtype_mem_card G _ (Finset.filter_subset _ _)

theorem edge_subtype_class_card {n l : ℕ} (G : WeldedInstance n) (b : EdgeClass) :
    (Finset.univ.filter (fun e : G.edges => G.bEdge l e.1 = some b)).card =
      (G.classEdges l b).card := by
  classical
  calc
    _ = (Finset.univ.filter (fun e : G.edges => e.1 ∈ G.classEdges l b)).card := by
      congr 1
      ext e
      simp [WeldedInstance.classEdges, e.2]
    _ = _ := edge_subtype_mem_card G _ (Finset.filter_subset _ _)

end WeldedPath.SwitchingCards

end


-- Solutions.SwitchingSurvival
section

namespace FinitePermutationCoupling

open scoped BigOperators

section RandomOrder

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every fixed item has the same chance of lying in a prescribed set of ranks
under a uniformly chosen order. This is an exact finite counting identity. -/
theorem uniform_perm_survival (S : Finset α) (x : α) :
    (∑ σ : Equiv.Perm α,
      if σ x ∈ S then 1 / (Fintype.card (Equiv.Perm α) : ℝ) else 0) =
        (S.card : ℝ) / (Fintype.card α : ℝ) := by
  classical
  let mass (y : α) : ℝ := ∑ σ : Equiv.Perm α, if σ y ∈ S then 1 else 0
  have hsame (y : α) : mass y = mass x := by
    apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap x y))
    intro σ
    simp [Equiv.Perm.mul_apply]
  have hone (σ : Equiv.Perm α) :
      (∑ y : α, if σ y ∈ S then (1 : ℝ) else 0) = S.card := by
    calc
      _ = ∑ y : α, if y ∈ S then (1 : ℝ) else 0 :=
        Fintype.sum_equiv σ _ _ (fun _ => rfl)
      _ = _ := by simp
  have htotal : (Fintype.card α : ℝ) * mass x =
      (Fintype.card (Equiv.Perm α) : ℝ) * S.card := by
    calc
      _ = ∑ y : α, mass y := by simp only [hsame, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      _ = ∑ σ : Equiv.Perm α, ∑ y : α, if σ y ∈ S then (1 : ℝ) else 0 :=
        Finset.sum_comm
      _ = _ := by simp only [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have ha : (Fintype.card α : ℝ) ≠ 0 := by
    have : Nonempty α := ⟨x⟩
    exact_mod_cast Fintype.card_ne_zero
  have hp : (Fintype.card (Equiv.Perm α) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hmass : (∑ σ : Equiv.Perm α,
      if σ x ∈ S then 1 / (Fintype.card (Equiv.Perm α) : ℝ) else 0) =
      mass x / (Fintype.card (Equiv.Perm α) : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs <;> simp
  rw [hmass]
  apply (div_eq_div_iff hp ha).mpr
  simpa only [mul_comm] using htotal

/-- Auxiliary process data can be correlated with the order. The uniform order
marginal alone determines the survival mass; independence is unnecessary. -/
theorem uniform_perm_survival_of_marginal {Ω : Type*} [Fintype Ω]
    (w : Equiv.Perm α → Ω → ℝ) (a : ℝ)
    (hrow : ∀ σ, (∑ ω, w σ ω) = a / (Fintype.card (Equiv.Perm α) : ℝ))
    (S : Finset α) (x : α) :
    (∑ σ : Equiv.Perm α, ∑ ω, if σ x ∈ S then w σ ω else 0) =
      ((S.card : ℝ) / (Fintype.card α : ℝ)) * a := by
  classical
  calc
    _ = ∑ σ : Equiv.Perm α,
        (if σ x ∈ S then 1 / (Fintype.card (Equiv.Perm α) : ℝ) else 0) * a := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hh : σ x ∈ S <;> simp [hh, hrow, div_eq_mul_inv, mul_comm]
    _ = (∑ σ : Equiv.Perm α,
        if σ x ∈ S then 1 / (Fintype.card (Equiv.Perm α) : ℝ) else 0) * a :=
      (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [uniform_perm_survival]

/-- With `r` of `m` ranks still active, a fixed item survives with probability
exactly `r/m`, including the first and last stages. -/
theorem uniform_order_survival (m r : ℕ) (hr : r ≤ m) (x : Fin m) :
    (∑ σ : Equiv.Perm (Fin m),
      if (σ x).val < r then 1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ) else 0) =
        (r : ℝ) / (m : ℝ) := by
  have hh := uniform_perm_survival (Finset.univ.filter (fun y : Fin m => y.val < r)) x
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.card_filter_val_lt, min_eq_right hr, Fintype.card_fin] using hh

theorem uniform_order_survival_of_marginal {Ω : Type*} [Fintype Ω]
    (m r : ℕ) (hr : r ≤ m) (w : Equiv.Perm (Fin m) → Ω → ℝ) (a : ℝ)
    (hrow : ∀ σ, (∑ ω, w σ ω) = a / (Fintype.card (Equiv.Perm (Fin m)) : ℝ))
    (x : Fin m) :
    (∑ σ : Equiv.Perm (Fin m), ∑ ω, if (σ x).val < r then w σ ω else 0) =
      ((r : ℝ) / (m : ℝ)) * a := by
  have hh := uniform_perm_survival_of_marginal w a hrow
    (Finset.univ.filter (fun y : Fin m => y.val < r)) x
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.card_filter_val_lt, min_eq_right hr, Fintype.card_fin] using hh

end RandomOrder

section Weighted

variable {Ω : Type*} [Fintype Ω]

/-- A bound conditional on activity combines with the activity marginal by a
finite weighted sum; the total mass `a` need not be normalized to one. -/
theorem weighted_activity_error_le (μ err : Ω → ℝ) (active : Ω → Prop)
    [DecidablePred active] (m r a : ℝ) (hm : 0 < m) (hr : 0 < r)
    (hlocal : ∀ ω, err ω ≤ (2 / r ^ 2) * (if active ω then μ ω else 0))
    (hsurvive : (∑ ω, if active ω then μ ω else 0) ≤ (r / m) * a) :
    (∑ ω, err ω) ≤ (2 / (m * r)) * a := by
  calc
    _ ≤ ∑ ω, (2 / r ^ 2) * (if active ω then μ ω else 0) :=
      Finset.sum_le_sum (fun ω _ => hlocal ω)
    _ = (2 / r ^ 2) * (∑ ω, if active ω then μ ω else 0) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2 / r ^ 2) * ((r / m) * a) :=
      mul_le_mul_of_nonneg_left hsurvive (by positivity)
    _ = _ := by field_simp

/-- The edge-class lower bound turns the survival-scaled local correction
error into the stage bound used by the switching-chain certificate. -/
theorem survival_scaled_le_dyadic (n m r : ℕ) (hn : 1 ≤ n)
    (hm : 2 ^ (n - 1) ≤ m) (hr : 0 < r) :
    2 / ((m : ℝ) * r) ≤ 4 / ((2 : ℝ) ^ n * r) := by
  have hmpos : 0 < m := lt_of_lt_of_le (pow_pos (by norm_num) _) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hpow : (2 : ℝ) ^ n ≤ 2 * m := by
    have hh : (2 : ℝ) ^ (n - 1) ≤ m := by exact_mod_cast hm
    have hn' : n = (n - 1) + 1 := by omega
    rw [hn', pow_succ]
    nlinarith
  apply (div_le_div_iff₀ (mul_pos hmR hrR) (mul_pos (by positivity) hrR)).mpr
  nlinarith

theorem weighted_activity_error_le_dyadic (μ err : Ω → ℝ) (active : Ω → Prop)
    [DecidablePred active] (n m r : ℕ) (a : ℝ) (ha : 0 ≤ a) (hn : 1 ≤ n)
    (hm : 2 ^ (n - 1) ≤ m) (hr : 0 < r)
    (hlocal : ∀ ω, err ω ≤ (2 / (r : ℝ) ^ 2) * (if active ω then μ ω else 0))
    (hsurvive : (∑ ω, if active ω then μ ω else 0) ≤ ((r : ℝ) / m) * a) :
    (∑ ω, err ω) ≤ (4 / ((2 : ℝ) ^ n * r)) * a := by
  have hmpos : 0 < m := lt_of_lt_of_le (pow_pos (by norm_num) _) hm
  have hh := weighted_activity_error_le μ err active (m : ℝ) (r : ℝ) a
    (by exact_mod_cast hmpos) (by exact_mod_cast hr) hlocal hsurvive
  exact hh.trans (mul_le_mul_of_nonneg_right (survival_scaled_le_dyadic n m r hn hm hr) ha)

end Weighted

end FinitePermutationCoupling

end


-- Solutions.WeldedPathSwitchingReduction
section

namespace WeldedPath

open Classical FinitePermutationCoupling SwitchingModel
open scoped BigOperators

set_option maxHeartbeats 800000

private theorem sum_fintype_eq {β : Type*} (I J : Fintype β) (f : β → ℝ) :
    @Finset.sum β ℝ _ (@Finset.univ β I) f =
      @Finset.sum β ℝ _ (@Finset.univ β J) f := by
  exact congrArg (fun K : Fintype β => @Finset.sum β ℝ _ (@Finset.univ β K) f)
    (Subsingleton.elim I J)

private theorem sum_fintype_congr {β : Type*} (I J : Fintype β)
    (f g : β → ℝ) (hfg : ∀ b, f b = g b) :
    @Finset.sum β ℝ _ (@Finset.univ β I) f =
      @Finset.sum β ℝ _ (@Finset.univ β J) g := by
  cases Subsingleton.elim I J
  exact Finset.sum_congr rfl (fun b _ => hfg b)

private theorem sum2_fintype_congr {β γ : Type*}
    (I J : Fintype β) (K L : Fintype γ)
    (f g : β → γ → ℝ) (hfg : ∀ b c, f b c = g b c) :
    @Finset.sum β ℝ _ (@Finset.univ β I)
        (fun b => @Finset.sum γ ℝ _ (@Finset.univ γ K) (f b)) =
      @Finset.sum β ℝ _ (@Finset.univ β J)
        (fun b => @Finset.sum γ ℝ _ (@Finset.univ γ L) (g b)) := by
  cases Subsingleton.elim I J
  cases Subsingleton.elim K L
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_congr rfl (fun c _ => hfg b c)

theorem single_cycle_switching_chain_reduction :
    ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedInstance n, G.IsValid → (G.singSupport l).Nonempty →
    ∃ v : Equiv.Perm G.edges →
        (Fin (2 ^ n + 1) → Equiv.Perm G.edges) → ℝ,
      (∀ h p, 0 ≤ v h p) ∧
      (∀ h, (∑ p, v h p) =
        if h ∈ ((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle) then
          1 / (((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle).card : ℝ)
        else 0) ∧
      (∀ h p, v h p ≠ 0 → p (Fin.last (2 ^ n)) = h) ∧
      (∀ g, (∑ h, ∑ p, if p 0 = g then v h p else 0) =
        if g ∈ Finset.univ.filter (G.IsEdgePerm l) then
          1 / ((Finset.univ.filter (G.IsEdgePerm l)).card : ℝ) else 0) ∧
      (∀ h (e : G.edges) (i : Fin (2 ^ n)),
        (∑ p, if (p i.castSucc) e ≠ (p i.succ) e then v h p else 0) ≤
          (4 / ((2 : ℝ) ^ n * ((i.val : ℝ) + 1))) *
            (if h ∈ ((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle) then
              1 / (((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle).card : ℝ)
            else 0)) := by
  intro n l hnEven hl hlo G hG hnonempty
  have hdensity (T : Finset (Equiv.Perm G.edges)) (h : Equiv.Perm G.edges) :
      density T h = if h ∈ T then 1 / (T.card : ℝ) else 0 := by
    unfold density
    split_ifs <;> rfl
  have hn : 1 ≤ n := by omega
  let S := (Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle
  have hclass (e : G.edges) (he : active G (block l G e)) :
      2 ^ (n - 1) ≤ (blockFiber (block l G) e).card ∧
        (blockFiber (block l G) e).card ≤ 2 ^ n := by
    rw [blockFiber_eq_weld l G e ((active_iff_weld l G e).mp he),
      SwitchingCards.edge_subtype_weld_card (l := l)]
    exact weld_color_class_card_bounds n l G hG hn (G.color e.1)
  have hcap : PartnerCap (block l G) (active G) S := by
    intro D h e z he heD
    rw [blockFiber_eq_weld l G e ((active_iff_weld l G e).mp he)]
    convert single_cycle_completion_count n l hnEven hl hlo G hG D h e z
      ((active_iff_weld l G e).mp he) heD using 1 <;>
      (try simp only [exposedFiber, S]) <;> congr <;> exact Subsingleton.elim _ _
  have hsub : S ⊆ blockSupport (block l G) := by
    rw [blockSupport_eq]
    exact Finset.filter_subset _ _
  obtain ⟨v, hv, hrow, hlast, hcol, hstep⟩ :=
    random_order_switching (block l G) (active G) S (2 ^ n)
      (by positivity) (edgeSing_nonempty l G hnonempty) hsub
      (singleCycle_saturated l G) hcap (fun e he => (hclass e he).2)
  refine ⟨v, hv, ?_, hlast, ?_, ?_⟩
  · intro h
    convert (hrow h).trans (hdensity S h) using 1
    exact sum_fintype_eq _ _ _
  · intro g
    have hh := (hcol g).trans (hdensity (blockSupport (block l G)) g)
    rw [blockSupport_eq] at hh
    convert hh using 1
    apply sum2_fintype_congr
    intro h p
    split_ifs <;> rfl
  · intro h e i
    have hnonneg : 0 ≤ density S h := by
      unfold density
      split_ifs <;> positivity
    have hbudget :
        (if active G (block l G e) then
          2 / (((blockFiber (block l G) e).card : ℝ) * ((i.val : ℝ) + 1))
        else 0) ≤ 4 / ((2 : ℝ) ^ n * ((i.val : ℝ) + 1)) := by
      split_ifs with he
      · have hh := survival_scaled_le_dyadic n (blockFiber (block l G) e).card
          (i.val + 1) hn (hclass e he).1 (by omega)
        simpa only [Nat.cast_add, Nat.cast_one] using hh
      · positivity
    have hh := (hstep h e i).trans (mul_le_mul_of_nonneg_right hbudget hnonneg)
    rw [hdensity] at hh
    convert hh using 1 <;>
      first
      | apply sum_fintype_congr
        intro p
        split_ifs <;> rfl
      | rfl

end WeldedPath

end

open Classical WeldedPath
open scoped BigOperators

theorem solution :
    ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedInstance n, G.IsValid → (G.singSupport l).Nonempty →
    ∃ v : Equiv.Perm G.edges →
        (Fin (2 ^ n + 1) → Equiv.Perm G.edges) → ℝ,
      (∀ h p, 0 ≤ v h p) ∧
      (∀ h, (∑ p, v h p) =
        if h ∈ ((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle) then
          1 / (((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle).card : ℝ)
        else 0) ∧
      (∀ h p, v h p ≠ 0 → p (Fin.last (2 ^ n)) = h) ∧
      (∀ g, (∑ h, ∑ p, if p 0 = g then v h p else 0) =
        if g ∈ Finset.univ.filter (G.IsEdgePerm l) then
          1 / ((Finset.univ.filter (G.IsEdgePerm l)).card : ℝ) else 0) ∧
      (∀ h (e : G.edges) (i : Fin (2 ^ n)),
        (∑ p, if (p i.castSucc) e ≠ (p i.succ) e then v h p else 0) ≤
          (4 / ((2 : ℝ) ^ n * ((i.val : ℝ) + 1))) *
            (if h ∈ ((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle) then
              1 / (((Finset.univ.filter (G.IsEdgePerm l)).filter G.SingleCycle).card : ℝ)
            else 0)) := by
  exact WeldedPath.single_cycle_switching_chain_reduction
