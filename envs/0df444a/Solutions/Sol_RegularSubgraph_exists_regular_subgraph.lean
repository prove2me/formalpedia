-- Prove2me | solution 1 for RegularSubgraph.exists_regular_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:29:51.1582+00:00
-- url     : https://prove2.me/submissions/53e81d27-0e55-46f9-a707-981d95e2156a

module
public import Mathlib
public import Definitions.Def_RegularSubgraphLib_RegularSubgraph
public import Theorems.Thm_RegularSubgraph_val_symm
public import Theorems.Thm_RegularSubgraph_adj_of_val_ne_zero
public import Theorems.Thm_RegularSubgraph_totalDegree_poly_le
public import Theorems.Thm_RegularSubgraph_eval_poly

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph MvPolynomial Finset
open RegularSubgraph
variable {V : Type*} [Fintype V]
namespace RegularSubgraph
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (hp : p.Prime)
    (hmax : ∀ v, G.degree v ≤ 2 * p - 1)
    (havg : (2 * p - 2) * Fintype.card V < 2 * #G.edgeFinset) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H ≠ ⊥ ∧
      ∀ v, (H.neighborSet v).ncard = 0 ∨ (H.neighborSet v).ncard = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  -- Chevalley–Warning
  have hdeg : (∑ v, (poly G p v).totalDegree) < Fintype.card (Edge G) := by
    have h1 : (∑ v, (poly G p v).totalDegree) ≤ Fintype.card V * (p - 1) := by
      calc (∑ v, (poly G p v).totalDegree) ≤ ∑ _v : V, (p - 1) :=
            Finset.sum_le_sum fun v _ => totalDegree_poly_le v
        _ = Fintype.card V * (p - 1) := by simp
    have h2 : Fintype.card (Edge G) = #G.edgeFinset := by
      rw [← Set.toFinset_card]
      exact congrArg Finset.card (by ext; simp)
    have h3 : (2 * p - 2) = 2 * (p - 1) := by omega
    rw [h2]
    rw [h3] at havg
    nlinarith
  have hdvd := char_dvd_card_solutions_of_fintype_sum_lt p hdeg
  -- a nonzero solution
  have hzero : ∀ v, eval (0 : Edge G → ZMod p) (poly G p v) = 0 := by
    intro v
    rw [eval_poly]
    have : #{w | val G p (0 : Edge G → ZMod p) v w ≠ 0} = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w _
      simp [val]
    rw [this, Nat.cast_zero]
  obtain ⟨x, hx, hx0⟩ : ∃ x : Edge G → ZMod p, (∀ v, eval x (poly G p v) = 0) ∧ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : Fintype.card { x : Edge G → ZMod p // ∀ v, eval x (poly G p v) = 0 } = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨0, hzero⟩, fun y => Subtype.ext (hcon y.1 y.2)⟩
    rw [hsub] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
  -- the subgraph
  let H : SimpleGraph V :=
    { Adj := fun a b => val G p x a b ≠ 0
      symm := ⟨fun a b h => by rwa [val_symm]⟩
      loopless := ⟨fun a h => G.loopless.irrefl a (adj_of_val_ne_zero h)⟩ }
  have hH : ∀ v, H.neighborSet v = ({w | val G p x v w ≠ 0} : Finset V) := by
    intro v; ext w; simp [H]
  refine ⟨H, fun a b h => adj_of_val_ne_zero h, ?_, fun v => ?_⟩
  · -- `H` is nonempty
    obtain ⟨e, he⟩ : ∃ e, x e ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx0 (funext hcon)
    obtain ⟨e, heG⟩ := e
    induction e using Sym2.ind with
    | h a b =>
      intro hbot
      have hab : val G p x a b ≠ 0 := by
        have hab' : G.Adj a b := heG
        simp only [val, hab', ↓reduceDIte]
        exact he
      have : H.Adj a b := hab
      rw [hbot] at this
      exact this
  · -- degrees are `0` or `p`
    rw [hH, Set.ncard_coe_finset]
    set m := #{w | val G p x v w ≠ 0}
    have hm : (m : ZMod p) = 0 := by rw [← eval_poly]; exact hx v
    rw [ZMod.natCast_eq_zero_iff] at hm
    have hle : m ≤ 2 * p - 1 := by
      refine le_trans ?_ (hmax v)
      rw [← card_neighborFinset_eq_degree]
      refine Finset.card_le_card fun w hw => ?_
      rw [Finset.mem_filter] at hw
      rw [mem_neighborFinset]
      exact adj_of_val_ne_zero hw.2
    obtain ⟨c, hc⟩ := hm
    have hc2 : c < 2 := by
      by_contra hc2
      have : p * 2 ≤ p * c := Nat.mul_le_mul_left _ (by omega)
      have := hp.one_lt
      omega
    interval_cases c
    · left; omega
    · right; omega
end RegularSubgraph
