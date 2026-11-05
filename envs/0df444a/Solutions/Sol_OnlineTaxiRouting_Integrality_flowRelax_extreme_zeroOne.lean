-- Prove2me | solution 1 for OnlineTaxiRouting.Integrality.flowRelax_extreme_zeroOne
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:04:50.838017+00:00
-- url     : https://prove2.me/submissions/606f1c14-d646-4ebb-a451-c9413818a8b5

import Mathlib
import Definitions.Def_OnlineTaxiRouting_Integrality_Setting

open Filter Topology

namespace TaxiFlowAux

/-- The integers, as an additive subgroup of `ℝ`. -/
abbrev G : AddSubgroup ℝ := (Int.castAddHom ℝ).range

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

/-- Net inflow at `v` of the arc function `f` (heads `hd`, tails `tl`). -/
def net (hd tl : E → V) (f : E → ℝ) (v : V) : ℝ :=
  (∑ e ∈ Finset.univ.filter (fun e => hd e = v), f e) -
    ∑ e ∈ Finset.univ.filter (fun e => tl e = v), f e

lemma sum_net (hd tl : E → V) (f : E → ℝ) : ∑ v, net hd tl f v = 0 := by
  unfold net
  rw [Finset.sum_sub_distrib, Finset.sum_fiberwise, Finset.sum_fiberwise, sub_self]

lemma net_eq_zero_of_ne (hd tl : E → V) (f : E → ℝ) (z : V)
    (h : ∀ v, v ≠ z → net hd tl f v = 0) : ∀ v, net hd tl f v = 0 := by
  intro v
  by_cases hv : v = z
  · subst hv
    have hs := sum_net hd tl f
    rwa [Finset.sum_eq_single v (fun b _ hb => h b hb) (by simp)] at hs
  · exact h v hv

lemma exists_circ [DecidableEq E] (hd tl : E → V) (f : E → ℝ) (hf : ∀ v, net hd tl f v = 0)
    (e0 : E) (he0 : f e0 ∉ G) :
    ∃ d : E → ℝ, d ≠ 0 ∧ (∀ v, net hd tl d v = 0) ∧ ∀ e, f e ∈ G → d e = 0 := by
  classical
  have hFmem : ∀ e, e ∈ Finset.univ.filter (fun e => f e ∉ G) ↔ f e ∉ G := by simp
  set F : Finset E := Finset.univ.filter (fun e => f e ∉ G) with hF
  set W : Finset V := F.image hd ∪ F.image tl with hW
  have he0F : e0 ∈ F := (hFmem e0).2 he0
  have hhdW : ∀ e ∈ F, hd e ∈ W := fun e he =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
  have htlW : ∀ e ∈ F, tl e ∈ W := fun e he =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
  have hw0 : hd e0 ∈ W := hhdW e0 he0F
  -- every vertex touched by a fractional arc has fractional degree at least two
  have hdeg : ∀ v ∈ W, 2 ≤ (F.filter (fun e => hd e = v)).card +
      (F.filter (fun e => tl e = v)).card := by
    intro v hv
    by_contra hlt
    push_neg at hlt
    have hpos : 0 < (F.filter (fun e => hd e = v)).card +
        (F.filter (fun e => tl e = v)).card := by
      rcases Finset.mem_union.1 hv with h | h
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
        have := Finset.card_pos.2 (⟨e, Finset.mem_filter.2 ⟨he, rfl⟩⟩ :
          (F.filter (fun e' => hd e' = hd e)).Nonempty)
        omega
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
        have := Finset.card_pos.2 (⟨e, Finset.mem_filter.2 ⟨he, rfl⟩⟩ :
          (F.filter (fun e' => tl e' = tl e)).Nonempty)
        omega
    have hkey : (∑ e ∈ F.filter (fun e => hd e = v), f e) -
        ∑ e ∈ F.filter (fun e => tl e = v), f e ∈ G := by
      have h0 := hf v
      unfold net at h0
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun e => hd e = v)
          (fun e => f e ∉ G),
        ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun e => tl e = v)
          (fun e => f e ∉ G)] at h0
      have e1 : (Finset.univ.filter fun e => hd e = v).filter (fun e => f e ∉ G) =
          F.filter (fun e => hd e = v) := by
        ext e; simp [hF, and_comm]
      have e2 : (Finset.univ.filter fun e => tl e = v).filter (fun e => f e ∉ G) =
          F.filter (fun e => tl e = v) := by
        ext e; simp [hF, and_comm]
      rw [e1, e2] at h0
      have hA : ∑ e ∈ (Finset.univ.filter fun e => hd e = v).filter (fun e => ¬ f e ∉ G),
          f e ∈ G := AddSubgroup.sum_mem _ (fun e he => by
            simp only [Finset.mem_filter, not_not] at he; exact he.2)
      have hB : ∑ e ∈ (Finset.univ.filter fun e => tl e = v).filter (fun e => ¬ f e ∉ G),
          f e ∈ G := AddSubgroup.sum_mem _ (fun e he => by
            simp only [Finset.mem_filter, not_not] at he; exact he.2)
      have := G.sub_mem hB hA
      convert this using 1
      linarith
    have hone : (F.filter (fun e => hd e = v)).card +
        (F.filter (fun e => tl e = v)).card = 1 := by omega
    rcases Nat.eq_zero_or_pos (F.filter (fun e => hd e = v)).card with ha | ha
    · rw [ha, zero_add] at hone
      obtain ⟨e1, he1⟩ := Finset.card_eq_one.1 hone
      rw [Finset.card_eq_zero.1 ha, he1, Finset.sum_empty, Finset.sum_singleton,
        zero_sub] at hkey
      have hmem : e1 ∈ F := (Finset.mem_filter.1 (he1 ▸ Finset.mem_singleton_self e1)).1
      have := G.neg_mem hkey
      rw [neg_neg] at this
      exact (hFmem e1).1 hmem this
    · have hb : (F.filter (fun e => tl e = v)).card = 0 := by omega
      have ha1 : (F.filter (fun e => hd e = v)).card = 1 := by omega
      obtain ⟨e1, he1⟩ := Finset.card_eq_one.1 ha1
      rw [Finset.card_eq_zero.1 hb, he1, Finset.sum_empty, Finset.sum_singleton,
        sub_zero] at hkey
      have hmem : e1 ∈ F := (Finset.mem_filter.1 (he1 ▸ Finset.mem_singleton_self e1)).1
      exact (hFmem e1).1 hmem hkey
  -- degree count: |W| ≤ |F|
  have h1 : F.card = ∑ v ∈ W, (F.filter (fun e => hd e = v)).card :=
    Finset.card_eq_sum_card_fiberwise hhdW
  have h2 : F.card = ∑ v ∈ W, (F.filter (fun e => tl e = v)).card :=
    Finset.card_eq_sum_card_fiberwise htlW
  have hWF : 2 * W.card ≤ 2 * F.card := by
    calc 2 * W.card = ∑ v ∈ W, 2 := by simp [mul_comm]
      _ ≤ ∑ v ∈ W, ((F.filter (fun e => hd e = v)).card +
          (F.filter (fun e => tl e = v)).card) := Finset.sum_le_sum hdeg
      _ = 2 * F.card := by rw [Finset.sum_add_distrib, ← h1, ← h2]; ring
  -- linear algebra
  let ext : ((↥F) → ℝ) →ₗ[ℝ] (E → ℝ) :=
    { toFun := fun g e => if h : e ∈ F then g ⟨e, h⟩ else 0
      map_add' := by intro a b; funext e; by_cases h : e ∈ F <;> simp [h]
      map_smul' := by intro r a; funext e; by_cases h : e ∈ F <;> simp [h] }
  let N : (E → ℝ) →ₗ[ℝ] (V → ℝ) :=
    { toFun := fun d v => net hd tl d v
      map_add' := by
        intro a b; funext v; simp only [net, Pi.add_apply, Finset.sum_add_distrib]; ring
      map_smul' := by
        intro r a; funext v
        simp [net, Finset.mul_sum, mul_sub] }
  let P : (V → ℝ) →ₗ[ℝ] ((↥(W.erase (hd e0))) → ℝ) := LinearMap.funLeft ℝ ℝ Subtype.val
  let M := P ∘ₗ N ∘ₗ ext
  have hrank : Module.finrank ℝ ((↥(W.erase (hd e0))) → ℝ) <
      Module.finrank ℝ ((↥F) → ℝ) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    rw [Finset.card_erase_of_mem hw0]
    have := Finset.card_pos.2 ⟨_, hw0⟩
    omega
  obtain ⟨g, hgM, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := M) hrank)
  have hext : ∀ e, ext g e = if h : e ∈ F then g ⟨e, h⟩ else 0 := fun e => rfl
  refine ⟨ext g, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, g i ≠ 0 := by
      by_contra h; push_neg at h; exact hg0 (funext h)
    intro h0
    apply hi
    have := congrFun h0 i.1
    rw [hext, dif_pos i.2] at this
    simpa using this
  · apply net_eq_zero_of_ne hd tl _ (hd e0)
    intro v hv
    by_cases hvW : v ∈ W
    · have hv' : v ∈ W.erase (hd e0) := Finset.mem_erase.2 ⟨hv, hvW⟩
      have := congrFun (LinearMap.mem_ker.1 hgM) ⟨v, hv'⟩
      exact this
    · unfold net
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
      · intro e he
        rw [hext, dif_neg]
        intro heF; apply hvW
        rw [← (Finset.mem_filter.1 he).2]; exact htlW e heF
      · intro e he
        rw [hext, dif_neg]
        intro heF; apply hvW
        rw [← (Finset.mem_filter.1 he).2]; exact hhdW e heF
  · intro e he
    rw [hext, dif_neg]
    intro h; exact (hFmem e).1 h he

end TaxiFlowAux

namespace TaxiFlowAux

/-- Vertices of the auxiliary network: `none` is the super source/sink `z`,
`some (inl k)` the taxi `k`, `some (inr (inl c))` the node `c_in`,
`some (inr (inr c))` the node `c_out`. -/
abbrev Vx (C K : Type*) := Option (K ⊕ C ⊕ C)
/-- Arcs: `σ_k` (z → k), `y_{k,c}` (k → c_in), `p_c` (c_in → c_out),
`x_{c',c}` (c'_out → c_in), `r_c` (c_out → z). -/
abbrev Ex (C K : Type*) := K ⊕ (K × C) ⊕ C ⊕ (C × C) ⊕ C

variable {C K : Type*}

def hdF : Ex C K → Vx C K
  | .inl k => some (.inl k)
  | .inr (.inl (_, c)) => some (.inr (.inl c))
  | .inr (.inr (.inl c)) => some (.inr (.inr c))
  | .inr (.inr (.inr (.inl (_, c)))) => some (.inr (.inl c))
  | .inr (.inr (.inr (.inr _))) => none

def tlF : Ex C K → Vx C K
  | .inl _ => none
  | .inr (.inl (k, _)) => some (.inl k)
  | .inr (.inr (.inl c)) => some (.inr (.inl c))
  | .inr (.inr (.inr (.inl (c', _)))) => some (.inr (.inr c'))
  | .inr (.inr (.inr (.inr c))) => some (.inr (.inr c))

variable [Fintype C] [Fintype K] [DecidableEq C] [DecidableEq K]

lemma net_k (f : Ex C K → ℝ) (k : K) :
    net hdF tlF f (some (.inl k)) = f (.inl k) - ∑ c, f (.inr (.inl (k, c))) := by
  rw [net, Finset.sum_filter, Finset.sum_filter]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, hdF, tlF]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
  simp

lemma net_cin (f : Ex C K → ℝ) (c : C) :
    net hdF tlF f (some (.inr (.inl c))) =
      (∑ k, f (.inr (.inl (k, c)))) + (∑ c', f (.inr (.inr (.inr (.inl (c', c)))))) -
        f (.inr (.inr (.inl c))) := by
  rw [net, Finset.sum_filter, Finset.sum_filter]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, hdF, tlF]

lemma net_cout (f : Ex C K → ℝ) (c : C) :
    net hdF tlF f (some (.inr (.inr c))) =
      f (.inr (.inr (.inl c))) -
        ((∑ c'', f (.inr (.inr (.inr (.inl (c, c'')))))) + f (.inr (.inr (.inr (.inr c))))) := by
  rw [net, Finset.sum_filter, Finset.sum_filter]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, hdF, tlF]
  rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
  simp

end TaxiFlowAux

namespace TaxiFlowAux
open OnlineTaxiRouting.Integrality

variable {C K : Type*} [Fintype C] [Fintype K]

/-- Arc values of the auxiliary circulation attached to a flow point `w = (x, y, p)`. -/
def arcVal (w : FlowVar C K) : Ex C K → ℝ
  | .inl k => ∑ c, w.2.1 k c
  | .inr (.inl (k, c)) => w.2.1 k c
  | .inr (.inr (.inl c)) => w.2.2 c
  | .inr (.inr (.inr (.inl (c', c)))) => w.1 c' c
  | .inr (.inr (.inr (.inr c))) => w.2.2 c - ∑ c'', w.1 c c''

lemma one_mem_G : (1 : ℝ) ∈ G := ⟨1, by simp⟩

lemma zero_one_of_G {a : ℝ} (h : a ∈ G) (h0 : 0 ≤ a) (h1 : a ≤ 1) : a = 0 ∨ a = 1 := by
  obtain ⟨n, rfl⟩ := h
  simp only [Int.coe_castAddHom] at *
  have h0' : (0 : ℤ) ≤ n := by exact_mod_cast h0
  have h1' : n ≤ 1 := by exact_mod_cast h1
  interval_cases n <;> simp

lemma ev_nonneg {a b : ℝ} (h0 : 0 ≤ a) (hG : a ∈ G → b = 0) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), 0 ≤ a + ε * b := by
  by_cases ha : a ∈ G
  · exact Filter.Eventually.of_forall fun ε => by rw [hG ha]; simpa using h0
  · have hpos : 0 < a := lt_of_le_of_ne h0 (fun h => ha (h ▸ G.zero_mem))
    have ht : Tendsto (fun ε : ℝ => a + ε * b) (𝓝 0) (𝓝 a) := by
      have hc : Continuous (fun ε : ℝ => a + ε * b) := by fun_prop
      simpa using hc.tendsto (0 : ℝ)
    exact (ht.eventually (lt_mem_nhds hpos)).mono fun _ h => h.le

lemma ev_box {a b : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (hG : a ∈ G → b = 0) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), 0 ≤ a + ε * b ∧ a + ε * b ≤ 1 := by
  have hu : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 ≤ (1 - a) + ε * (-b) := by
    refine ev_nonneg (by linarith) (fun h => ?_)
    have : a ∈ G := by have := G.sub_mem one_mem_G h; simpa using this
    rw [hG this, neg_zero]
  filter_upwards [ev_nonneg h0 hG, hu] with ε h1 h2
  constructor
  · exact h1
  · linarith

theorem flow_main (A : C → C → Prop) (B : K → C → Prop) :
    ∀ w ∈ Set.extremePoints ℝ (flowRelax A B), IsZeroOneFlow w := by
  classical
  intro w hw
  obtain ⟨hwS, hext⟩ := mem_extremePoints.1 hw
  obtain ⟨h6, h7, h8, hx, hy, hp, hA, hB⟩ := hwS
  by_contra hz
  have hcirc : ∀ v, net hdF tlF (arcVal w) v = 0 := by
    apply net_eq_zero_of_ne _ _ _ none
    intro v hv
    rcases v with _ | (k | c | c)
    · exact absurd rfl hv
    · rw [net_k]; simp [arcVal]
    · rw [net_cin]; simp only [arcVal]; linarith [h6 c]
    · rw [net_cout]; simp [arcVal]
  obtain ⟨e0, he0⟩ : ∃ e0, arcVal w e0 ∉ G := by
    by_contra hall
    push_neg at hall
    apply hz
    exact ⟨fun c' c => zero_one_of_G (hall (.inr (.inr (.inr (.inl (c', c))))))
        (hx c' c).1 (hx c' c).2,
      fun k c => zero_one_of_G (hall (.inr (.inl (k, c)))) (hy k c).1 (hy k c).2,
      fun c => zero_one_of_G (hall (.inr (.inr (.inl c)))) (hp c).1 (hp c).2⟩
  obtain ⟨d, hd0, hdc, hdG⟩ := exists_circ hdF tlF (arcVal w) hcirc e0 he0
  obtain ⟨dw, hdw⟩ : ∃ dw : FlowVar C K, dw =
      (fun c' c => d (.inr (.inr (.inr (.inl (c', c))))), fun k c => d (.inr (.inl (k, c))),
        fun c => d (.inr (.inr (.inl c)))) := ⟨_, rfl⟩
  have hdx : ∀ c' c, dw.1 c' c = d (.inr (.inr (.inr (.inl (c', c))))) := by simp [hdw]
  have hdy : ∀ k c, dw.2.1 k c = d (.inr (.inl (k, c))) := by simp [hdw]
  have hdp : ∀ c, dw.2.2 c = d (.inr (.inr (.inl c))) := by simp [hdw]
  have dk : ∀ k, d (.inl k) = ∑ c, d (.inr (.inl (k, c))) := fun k => by
    have := hdc (some (.inl k)); rw [net_k] at this; linarith
  have dcin : ∀ c, d (.inr (.inr (.inl c))) =
      (∑ k, d (.inr (.inl (k, c)))) + ∑ c', d (.inr (.inr (.inr (.inl (c', c))))) := fun c => by
    have := hdc (some (.inr (.inl c))); rw [net_cin] at this; linarith
  have dcout : ∀ c, d (.inr (.inr (.inr (.inr c)))) =
      d (.inr (.inr (.inl c))) - ∑ c'', d (.inr (.inr (.inr (.inl (c, c''))))) := fun c => by
    have := hdc (some (.inr (.inr c))); rw [net_cout] at this; linarith
  have hdw0 : dw ≠ 0 := by
    intro h0
    have ex : ∀ c' c, d (.inr (.inr (.inr (.inl (c', c))))) = 0 := fun c' c => by
      rw [← hdx, h0]; rfl
    have ey : ∀ k c, d (.inr (.inl (k, c))) = 0 := fun k c => by
      rw [← hdy, h0]; rfl
    have ep : ∀ c, d (.inr (.inr (.inl c))) = 0 := fun c => by
      rw [← hdp, h0]; rfl
    apply hd0
    funext e
    rcases e with k | ⟨k, c⟩ | c | ⟨c', c⟩ | c
    · rw [dk]; simp [ey]
    · exact ey k c
    · exact ep c
    · exact ex c' c
    · rw [dcout]; simp [ex, ep]
  have H : ∀ᶠ ε in 𝓝 (0 : ℝ), w + ε • dw ∈ flowRelax A B := by
    simp only [flowRelax, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hdx, hdy, hdp,
      Filter.eventually_and, Filter.eventually_all]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c
      refine Filter.Eventually.of_forall fun ε => ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        h6 c, dcin c]
      ring
    · intro c'
      have hr : 0 ≤ arcVal w (.inr (.inr (.inr (.inr c')))) := by
        simp only [arcVal]; linarith [h7 c']
      filter_upwards [ev_nonneg hr (hdG _)] with ε hε
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [dcout] at hε
      simp only [arcVal] at hε
      linarith [mul_sub ε (d (.inr (.inr (.inl c'))))
        (∑ c'', d (.inr (.inr (.inr (.inl (c', c''))))))]
    · intro k
      have hs : 0 ≤ 1 - arcVal w (.inl k) := by simp only [arcVal]; linarith [h8 k]
      have hsG : 1 - arcVal w (.inl k) ∈ G → -d (.inl k) = 0 := fun h => by
        have : arcVal w (.inl k) ∈ G := by have := G.sub_mem one_mem_G h; simpa using this
        rw [hdG _ this, neg_zero]
      filter_upwards [ev_nonneg hs hsG] with ε hε
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← dk k]
      simp only [arcVal] at hε
      linarith
    · intro c' c
      exact Filter.eventually_and.1
        (ev_box (hx c' c).1 (hx c' c).2 (hdG (.inr (.inr (.inr (.inl (c', c)))))))
    · intro k c
      exact Filter.eventually_and.1 (ev_box (hy k c).1 (hy k c).2 (hdG (.inr (.inl (k, c)))))
    · intro c
      exact Filter.eventually_and.1 (ev_box (hp c).1 (hp c).2 (hdG (.inr (.inr (.inl c)))))
    · intro c' c hn
      refine Filter.Eventually.of_forall fun ε => ?_
      have h0 : w.1 c' c = 0 := hA c' c hn
      have : d (.inr (.inr (.inr (.inl (c', c))))) = 0 :=
        hdG _ (by show w.1 c' c ∈ G; rw [h0]; exact G.zero_mem)
      rw [h0, this]; ring
    · intro k c hn
      refine Filter.Eventually.of_forall fun ε => ?_
      have h0 : w.2.1 k c = 0 := hB k c hn
      have : d (.inr (.inl (k, c))) = 0 :=
        hdG _ (by show w.2.1 k c ∈ G; rw [h0]; exact G.zero_mem)
      rw [h0, this]; ring
  have H2 : ∀ᶠ ε in 𝓝 (0 : ℝ), w + (-ε) • dw ∈ flowRelax A B := by
    have ht : Tendsto (fun ε : ℝ => -ε) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact ht.eventually H
  have H3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (w + ε • dw ∈ flowRelax A B ∧ w + (-ε) • dw ∈ flowRelax A B) ∧ ε ∈ Set.Ioi 0 :=
    ((H.and H2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨ε, ⟨h1, h2⟩, hεpos⟩ := H3.exists
  have hseg : w ∈ openSegment ℝ (w + ε • dw) (w + (-ε) • dw) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  have h3 := (hext _ h1 _ h2 hseg).1
  have h4 : ε • dw = 0 := by simpa using h3
  rcases smul_eq_zero.1 h4 with h | h
  · exact absurd h (ne_of_gt hεpos)
  · exact hdw0 h

end TaxiFlowAux

open OnlineTaxiRouting.Integrality in
theorem solution {C K : Type*} [Fintype C] [Fintype K]
    (A : C → C → Prop) (B : K → C → Prop) :
    ∀ w ∈ Set.extremePoints ℝ (flowRelax A B), IsZeroOneFlow w :=
  TaxiFlowAux.flow_main A B
