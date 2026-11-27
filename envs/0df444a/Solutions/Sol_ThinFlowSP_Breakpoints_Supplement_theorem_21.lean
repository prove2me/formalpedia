-- Prove2me | solution 1 for ThinFlowSP.Breakpoints.Supplement.theorem_21
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:54.760809+00:00
-- url     : https://prove2.me/submissions/b6958a1f-d3ac-4bb9-97ad-ddeefb203c17

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Network
import Definitions.Def_ThinFlowSP_Breakpoints_Model
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_FluidModel
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_DE
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_RightMonotone

open MeasureTheory

open ThinFlowSP
open ThinFlowSP.Breakpoints
open ThinFlowSP.Breakpoints.Supplement

theorem solution (N : QNet) (hN : N.Standing) (ν0 : ℝ → ℝ) (hν0 : IsInflowRate ν0)
    (hrm : RightMonotone ν0) (ϑ : ℝ) (hϑ : 0 ≤ ϑ) (ℓ : ℝ → N.G.V → ℝ)
    (hℓ : SolvesDEUpTo N ν0 ϑ ℓ) :
    ∃ α > 0, ∃ ℓ' : ℝ → N.G.V → ℝ,
      (∀ θ ≤ ϑ, ℓ' θ = ℓ θ) ∧ SolvesDEUpTo N ν0 (ϑ + α) ℓ' := by
        classical
        have hNstanding := hN
        obtain ⟨hst, hν, hτ, hacyc0, hreach⟩ := hN
        have hAcyc : ∀ L : N.G.V → ℝ, IsAcyclic (Gprime N L) := by
          intro L
          have key : ∀ u w, Relation.TransGen (Adj (Gprime N L)) u w →
              L u ≤ L w ∧ (L u = L w →
                Relation.TransGen (Adj (subNet N.G (Finset.univ.filter fun a => N.τ a = 0))) u w) := by
            intro u w h
            induction h with
            | single hab =>
              obtain ⟨b, hb1, hb2⟩ := hab
              have hb := b.2
              simp only [primeArcs, Finset.mem_filter, Finset.mem_univ, true_and] at hb
              have h0 := hτ b.1
              have e1 : N.G.tail b.1 = _ := hb1
              have e2 : N.G.head b.1 = _ := hb2
              rw [e1, e2] at hb
              refine ⟨by linarith, fun heq => ?_⟩
              have hz : N.τ b.1 = 0 := by linarith
              exact Relation.TransGen.single ⟨⟨b.1, by simp [hz]⟩, e1, e2⟩
            | @tail x y _ hab ih =>
              obtain ⟨b, hb1, hb2⟩ := hab
              have hb := b.2
              simp only [primeArcs, Finset.mem_filter, Finset.mem_univ, true_and] at hb
              have h0 := hτ b.1
              have e1 : N.G.tail b.1 = _ := hb1
              have e2 : N.G.head b.1 = _ := hb2
              rw [e1, e2] at hb
              obtain ⟨ih1, ih2⟩ := ih
              refine ⟨by linarith, fun heq => ?_⟩
              have hz : N.τ b.1 = 0 := by linarith
              have hx : L u = L x := by linarith
              exact Relation.TransGen.tail (ih2 hx) ⟨⟨b.1, by simp [hz]⟩, e1, e2⟩
          intro v hv
          exact hacyc0 v ((key v v hv).2 rfl)
        have hACmin : ∀ (g : ℝ → ℝ) (c : ℝ) (a b : ℝ),
            AbsolutelyContinuousOnInterval g (min a c) (min b c) →
            AbsolutelyContinuousOnInterval (fun θ => g (min θ c)) a b := by
          intro g c a b hg
          rw [absolutelyContinuousOnInterval_iff] at hg ⊢
          intro ε hε
          obtain ⟨δ, hδ, h⟩ := hg ε hε
          refine ⟨δ, hδ, fun E hE hlen => ?_⟩
          have hE' : ((E.1, fun i => (min (E.2 i).1 c, min (E.2 i).2 c)) : ℕ × (ℕ → ℝ × ℝ)) ∈
              AbsolutelyContinuousOnInterval.disjWithin (min a c) (min b c) := by
            obtain ⟨h1, h2⟩ := hE
            refine ⟨fun i hi => ?_, ?_⟩
            · obtain ⟨h1a, h1b⟩ := h1 i hi
              simp only [Set.mem_uIcc] at h1a h1b ⊢
              constructor
              · rcases h1a with ⟨x, y⟩ | ⟨x, y⟩
                · left; exact ⟨min_le_min_right _ x, min_le_min_right _ y⟩
                · right; exact ⟨min_le_min_right _ x, min_le_min_right _ y⟩
              · rcases h1b with ⟨x, y⟩ | ⟨x, y⟩
                · left; exact ⟨min_le_min_right _ x, min_le_min_right _ y⟩
                · right; exact ⟨min_le_min_right _ x, min_le_min_right _ y⟩
            · intro i hi j hj hij
              have hsub : ∀ x y : ℝ, Set.uIoc (min x c) (min y c) ⊆ Set.uIoc x y := by
                intro x y t ht
                simp only [Set.mem_uIoc] at ht ⊢
                rcases ht with ⟨p, q⟩ | ⟨p, q⟩
                · left
                  refine ⟨?_, le_trans q (min_le_left _ _)⟩
                  by_contra hx; push Not at hx
                  have : min x c = x := min_eq_left (by
                    by_contra hc; push Not at hc
                    have := min_le_right y c; rw [min_eq_right hc.le] at p; linarith)
                  linarith
                · right
                  refine ⟨?_, le_trans q (min_le_left _ _)⟩
                  by_contra hx; push Not at hx
                  have : min y c = y := min_eq_left (by
                    by_contra hc; push Not at hc
                    have := min_le_right x c; rw [min_eq_right hc.le] at p; linarith)
                  linarith
              exact Set.disjoint_of_subset (hsub _ _) (hsub _ _) (h2 hi hj hij)
          have hl : ∑ i ∈ Finset.range E.1, dist (min (E.2 i).1 c) (min (E.2 i).2 c) < δ := by
            refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ => ?_) hlen
            rw [Real.dist_eq, Real.dist_eq]
            exact abs_min_sub_min_le_max _ _ _ _ |>.trans (by simp)
          exact h _ hE' hl
        by_cases hSPG : IsShortestPathGraph (Gprime N (ℓ ϑ))
        ·
          have A_sum : ∀ (G : Net) (W : Finset G.V) (y : G.A → ℝ),
              ∑ w ∈ W, (inflow G y w - outflow G y w) =
                ∑ a, y a * ((if G.head a ∈ W then 1 else 0) - (if G.tail a ∈ W then 1 else 0)) := by
            clear * -
            intro G W y
            have key : ∀ f : G.A → G.V, ∑ w ∈ W, ∑ a ∈ Finset.univ.filter (fun a => f a = w), y a =
                ∑ a, y a * (if f a ∈ W then 1 else 0) := by
              intro f
              simp_rw [Finset.sum_filter]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.sum_ite_eq]
              split_ifs <;> simp
            unfold inflow outflow
            rw [Finset.sum_sub_distrib, key, key, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring
          have A_bdd : ∀ (N : QNet) (_ : N.Standing) (T0 : N.G.A → ℝ) (c M : ℝ) (_ : 0 ≤ M) (v : N.G.V),
              ∃ B : ℝ, ∀ (l : N.G.V → ℝ) (y : N.G.A → ℝ), l N.G.s = c → (∀ a, 0 ≤ y a) →
                (∀ a, l (N.G.head a) ≤ l (N.G.tail a) → y a = 0) →
                (∀ w, w ≠ N.G.s → inflow N.G y w - outflow N.G y w ≤ if w = N.G.t then M else 0) →
                (∀ a, y a ≤ M → l (N.G.head a) ≤ max (l (N.G.tail a) + N.τ a + M) (T0 a + M / N.ν a)) →
                l v ≤ B := by
            clear * - A_sum
            intro N hN T0 c M hM v
            obtain ⟨_, hν, hτ, _, hr⟩ := hN
            have h := hr v
            unfold Reaches at h
            induction h with
            | refl => exact ⟨c, fun l y h1 _ _ _ _ => h1.le⟩
            | @tail u w _ hadj ih =>
              obtain ⟨B, hB⟩ := ih
              obtain ⟨a0, ha1, ha2⟩ := hadj
              refine ⟨max (max B c) (max (max B c + N.τ a0 + M) (T0 a0 + M / N.ν a0)), ?_⟩
              intro l y h1 h2 h3 h4 h5
              by_contra hcon
              push Not at hcon
              have hu : l u ≤ max B c := (hB l y h1 h2 h3 h4 h5).trans (le_max_left _ _)
              have hw1 : max B c < l w := lt_of_le_of_lt (le_max_left _ _) hcon
              have hw2 := lt_of_le_of_lt (le_max_right _ _) hcon
              have hsum := A_sum N.G (Finset.univ.filter fun v => max B c < l v) y
              have hle : ∑ w ∈ (Finset.univ.filter fun v => max B c < l v),
                  (inflow N.G y w - outflow N.G y w) ≤ M := by
                calc _ ≤ ∑ w ∈ (Finset.univ.filter fun v => max B c < l v), (if w = N.G.t then M else 0) := by
                      refine Finset.sum_le_sum fun w hw => h4 w ?_
                      rintro rfl
                      rw [Finset.mem_filter, h1] at hw
                      exact absurd hw.2 (not_lt.2 (le_max_right _ _))
                  _ ≤ M := by
                      rw [Finset.sum_ite_eq']
                      split_ifs
                      · exact le_rfl
                      · exact hM
              have hge : y a0 ≤ ∑ a, y a * ((if N.G.head a ∈ (Finset.univ.filter fun v => max B c < l v) then (1:ℝ) else 0) - (if N.G.tail a ∈ (Finset.univ.filter fun v => max B c < l v) then 1 else 0)) := by
                have h0 : y a0 * ((if N.G.head a0 ∈ (Finset.univ.filter fun v => max B c < l v) then (1:ℝ) else 0) - (if N.G.tail a0 ∈ (Finset.univ.filter fun v => max B c < l v) then 1 else 0)) = y a0 := by
                  rw [ha1, ha2, if_pos (by simpa using hw1), if_neg (show u ∉ (Finset.univ.filter fun v => max B c < l v) from fun hm => absurd (Finset.mem_filter.1 hm).2 (not_lt.2 hu))]
                  ring
                rw [← h0]
                refine Finset.single_le_sum (f := fun a => y a * ((if N.G.head a ∈ (Finset.univ.filter fun v => max B c < l v) then (1:ℝ) else 0) - (if N.G.tail a ∈ (Finset.univ.filter fun v => max B c < l v) then 1 else 0))) ?_ (Finset.mem_univ a0)
                intro a _
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                by_cases p : max B c < l (N.G.head a) <;> by_cases q : max B c < l (N.G.tail a)
                · rw [if_pos p, if_pos q]; simp
                · rw [if_pos p, if_neg q]; simpa using h2 a
                · rw [h3 a (by linarith [not_lt.1 p])]; simp
                · rw [if_neg p, if_neg q]; simp
              have hyM : y a0 ≤ M := by linarith
              have h6 := h5 a0 hyM
              rw [ha1, ha2] at h6
              have : max (l u + N.τ a0 + M) (T0 a0 + M / N.ν a0) ≤ max (max B c + N.τ a0 + M) (T0 a0 + M / N.ν a0) :=
                max_le_max (by linarith) le_rfl
              linarith
          have A_max : ∀ (N : QNet) (_ : N.Standing) (T0 : N.G.A → ℝ) (c M : ℝ) (_ : 0 ≤ M)
              (K L : ℝ) (_ : 1 ≤ K) (_ : L ≤ c) (_ : ∀ a, L ≤ T0 a),
              ∃ (l : N.G.V → ℝ) (y : N.G.A → ℝ), l N.G.s = c ∧ (∀ v, L ≤ l v) ∧
                (∀ a, y a = min (N.ν a * max (l (N.G.head a) - T0 a) 0)
                  (K * max (l (N.G.head a) - l (N.G.tail a) - N.τ a) 0)) ∧
                (∀ w, w ≠ N.G.s → inflow N.G y w - outflow N.G y w = if w = N.G.t then M else 0) ∧
                (∀ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ max (l (N.G.tail a) + N.τ a) (T0 a) ≤ l w) := by
            clear * - A_bdd
            intro N hN T0 c M hM K L hK hLc hLT
            have hbdd := A_bdd N hN T0 c M hM
            obtain ⟨_, hν, hτ, _, _⟩ := hN
            choose B hB using hbdd
            obtain ⟨Y, hY⟩ : ∃ Y : (N.G.V → ℝ) → N.G.A → ℝ, ∀ l a, Y l a =
                min (N.ν a * max (l (N.G.head a) - T0 a) 0)
                  (K * max (l (N.G.head a) - l (N.G.tail a) - N.τ a) 0) := ⟨_, fun _ _ => rfl⟩
            have hK0 : 0 ≤ K := by linarith
            have hYc : ∀ a, Continuous fun l => Y l a := by
              intro a
              simp_rw [hY]
              fun_prop
            have hY0 : ∀ l a, 0 ≤ Y l a := by
              intro l a
              rw [hY]
              exact le_min (mul_nonneg (hν a).le (le_max_right _ _)) (mul_nonneg hK0 (le_max_right _ _))
            have hYz : ∀ l a, l (N.G.head a) ≤ max (l (N.G.tail a) + N.τ a) (T0 a) → Y l a = 0 := by
              intro l a h
              refine le_antisymm ?_ (hY0 l a)
              rw [hY]
              rcases le_max_iff.1 h with h | h
              · refine (min_le_right _ _).trans ?_
                rw [max_eq_right (by linarith)]; simp
              · refine (min_le_left _ _).trans ?_
                rw [max_eq_right (by linarith)]; simp
            have hin0 : ∀ l w, 0 ≤ inflow N.G (Y l) w := fun l w => Finset.sum_nonneg fun a _ => hY0 l a
            have hout0 : ∀ l w, 0 ≤ outflow N.G (Y l) w := fun l w => Finset.sum_nonneg fun a _ => hY0 l a
            have hec : ∀ w, Continuous fun l => inflow N.G (Y l) w - outflow N.G (Y l) w := by
              intro w
              unfold inflow outflow
              exact (continuous_finsetSum _ fun a _ => hYc a).sub (continuous_finsetSum _ fun a _ => hYc a)
            have hb0 : ∀ w, (0:ℝ) ≤ if w = N.G.t then M else 0 := by
              intro w; split_ifs
              · exact hM
              · exact le_rfl
            obtain ⟨S, hS⟩ : ∃ S : Set (N.G.V → ℝ), S = {l | l N.G.s = c ∧ (∀ v, L ≤ l v) ∧
                ∀ w, w ≠ N.G.s → inflow N.G (Y l) w - outflow N.G (Y l) w ≤ if w = N.G.t then M else 0} :=
              ⟨_, rfl⟩
            have hSB : S ⊆ Set.pi Set.univ fun v => Set.Icc L (B v) := by
              intro l hl v _
              rw [hS] at hl
              refine ⟨hl.2.1 v, hB v l (Y l) hl.1 (hY0 l) ?_ hl.2.2 ?_⟩
              · intro a h
                exact hYz l a (le_max_of_le_left (by linarith [hτ a]))
              · intro a h
                rw [hY] at h
                rcases min_le_iff.1 h with h | h
                · refine le_max_of_le_right ?_
                  have h1 : N.ν a * (l (N.G.head a) - T0 a) ≤ M :=
                    (mul_le_mul_of_nonneg_left (le_max_left _ _) (hν a).le).trans h
                  have h2 : l (N.G.head a) - T0 a ≤ M / N.ν a := by
                    rw [le_div_iff₀ (hν a)]; linarith
                  linarith
                · refine le_max_of_le_left ?_
                  have h1 : max (l (N.G.head a) - l (N.G.tail a) - N.τ a) 0 ≤ M := by
                    nlinarith [le_max_right (l (N.G.head a) - l (N.G.tail a) - N.τ a) 0]
                  linarith [le_max_left (l (N.G.head a) - l (N.G.tail a) - N.τ a) 0]
            have hScl : IsClosed S := by
              have : S = {l | l N.G.s = c} ∩ ((⋂ v, {l | L ≤ l v}) ∩ ⋂ w, ⋂ (_ : w ≠ N.G.s),
                  {l | inflow N.G (Y l) w - outflow N.G (Y l) w ≤ if w = N.G.t then M else 0}) := by
                rw [hS]; ext l; simp
              rw [this]
              refine (isClosed_eq (continuous_apply _) continuous_const).inter (IsClosed.inter ?_ ?_)
              · exact isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)
              · exact isClosed_iInter fun w => isClosed_iInter fun _ => isClosed_le (hec w) continuous_const
            have hSc : IsCompact S :=
              (isCompact_univ_pi fun v => isCompact_Icc).of_isClosed_subset hScl hSB
            have hSne : S.Nonempty := by
              refine ⟨fun v => if v = N.G.s then c else L, ?_⟩
              rw [hS]
              refine ⟨by simp, ?_, ?_⟩
              · intro v
                dsimp only
                split_ifs
                · exact hLc
                · exact le_rfl
              · intro w hw
                have h1 : inflow N.G (Y fun v => if v = N.G.s then c else L) w = 0 := by
                  refine Finset.sum_eq_zero fun a ha => hYz _ a (le_max_of_le_right ?_)
                  rw [Finset.mem_filter] at ha
                  rw [ha.2, if_neg hw]
                  exact hLT a
                rw [h1]
                linarith [hout0 (fun v => if v = N.G.s then c else L) w, hb0 w]
            obtain ⟨l, hlS, hlmax⟩ := hSc.exists_isMaxOn hSne
              (f := fun l => ∑ v, l v) (by fun_prop)
            have hl := hlS
            rw [hS] at hl
            obtain ⟨hl1, hl2, hl3⟩ := hl
            have hraise : ∀ w, w ≠ N.G.s → ∀ ε > 0,
                (if w = N.G.t then M else 0) < inflow N.G (Y (Function.update l w (l w + ε))) w
                  - outflow N.G (Y (Function.update l w (l w + ε))) w := by
              intro w hw ε hε
              by_contra hcon
              push Not at hcon
              have hmem : Function.update l w (l w + ε) ∈ S := by
                rw [hS]
                refine ⟨?_, ?_, ?_⟩
                · rw [Function.update_of_ne (Ne.symm hw)]; exact hl1
                · intro v
                  by_cases hv : v = w
                  · subst hv; rw [Function.update_self]; linarith [hl2 v]
                  · rw [Function.update_of_ne hv]; exact hl2 v
                · intro u hu
                  by_cases huw : u = w
                  · subst huw; exact hcon
                  refine le_trans ?_ (hl3 u hu)
                  have hup : ∀ v, l v ≤ Function.update l w (l w + ε) v := by
                    intro v
                    by_cases hv : v = w
                    · subst hv; rw [Function.update_self]; linarith
                    · rw [Function.update_of_ne hv]
                  have h1 : inflow N.G (Y (Function.update l w (l w + ε))) u ≤ inflow N.G (Y l) u := by
                    refine Finset.sum_le_sum fun a ha => ?_
                    rw [Finset.mem_filter] at ha
                    rw [hY, hY, ha.2, Function.update_of_ne huw]
                    refine min_le_min le_rfl (mul_le_mul_of_nonneg_left (max_le_max ?_ le_rfl) hK0)
                    linarith [hup (N.G.tail a)]
                  have h2 : outflow N.G (Y l) u ≤ outflow N.G (Y (Function.update l w (l w + ε))) u := by
                    refine Finset.sum_le_sum fun a ha => ?_
                    rw [Finset.mem_filter] at ha
                    rw [hY, hY, ha.2, Function.update_of_ne huw]
                    refine min_le_min (mul_le_mul_of_nonneg_left (max_le_max ?_ le_rfl) (hν a).le)
                      (mul_le_mul_of_nonneg_left (max_le_max ?_ le_rfl) hK0) <;>
                    linarith [hup (N.G.head a)]
                  linarith
              have h1 := hlmax hmem
              have h2 : ∑ v, Function.update l w (l w + ε) v = ∑ v, l v + ε := by
                rw [Finset.sum_update_of_mem (Finset.mem_univ w), ← Finset.add_sum_erase _ l (Finset.mem_univ w), Finset.sdiff_singleton_eq_erase]
                ring
              simp only [Set.mem_ofPred_eq] at h1
              linarith
            refine ⟨l, Y l, hl1, hl2, hY l, ?_, ?_⟩
            · intro w hw
              refine le_antisymm (hl3 w hw) ?_
              by_contra hcon
              push Not at hcon
              have hcont : Continuous fun ε : ℝ => inflow N.G (Y (Function.update l w (l w + ε))) w
                  - outflow N.G (Y (Function.update l w (l w + ε))) w :=
                (hec w).comp (continuous_const.update w (by fun_prop))
              have h0 : inflow N.G (Y (Function.update l w (l w + 0))) w
                  - outflow N.G (Y (Function.update l w (l w + 0))) w < if w = N.G.t then M else 0 := by
                rw [add_zero, Function.update_eq_self]; exact hcon
              have hev := hcont.continuousAt.eventually (gt_mem_nhds h0)
              obtain ⟨ε, hε1, hε2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
                (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ nhdsWithin 0 (Set.Ioi 0))).exists
              exact lt_asymm hε1 (hraise w hw ε hε2)
            · intro w hw
              by_contra hcon
              push Not at hcon
              have hev : ∀ᶠ ε : ℝ in nhds 0, ∀ a, N.G.head a = w →
                  l w + ε < max (l (N.G.tail a) + N.τ a) (T0 a) := by
                rw [Filter.eventually_all]
                intro a
                by_cases ha : N.G.head a = w
                · have hc : Continuous fun ε : ℝ => l w + ε := by fun_prop
                  have h0 : l w + 0 < max (l (N.G.tail a) + N.τ a) (T0 a) := by
                    rw [add_zero]; exact hcon a ha
                  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds h0)] with ε hε _ using hε
                · exact Filter.Eventually.of_forall fun ε h => absurd h ha
              obtain ⟨ε, hε1, hε2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
                (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ nhdsWithin 0 (Set.Ioi 0))).exists
              have hε2' : 0 < ε := hε2
              have h1 := hraise w hw ε hε2
              have h2 : inflow N.G (Y (Function.update l w (l w + ε))) w = 0 := by
                refine Finset.sum_eq_zero fun a ha => hYz _ a ?_
                rw [Finset.mem_filter] at ha
                rw [ha.2, Function.update_self]
                by_cases ht : N.G.tail a = w
                · rw [ht, Function.update_self]
                  exact le_max_of_le_left (by linarith [hτ a])
                · rw [Function.update_of_ne ht]
                  exact (hε1 a ha.2).le
              linarith [hout0 (Function.update l w (l w + ε)) w, hb0 w]
          have step_exists : ∀ (N : QNet) (_ : N.Standing) (T0 : N.G.A → ℝ) (c M : ℝ) (_ : 0 ≤ M),
              ∃ (l : N.G.V → ℝ) (y : N.G.A → ℝ), l N.G.s = c ∧ (∀ a, 0 ≤ y a) ∧
                (∀ v, outflow N.G y v - inflow N.G y v =
                  (if v = N.G.s then M else 0) - (if v = N.G.t then M else 0)) ∧
                (∀ a, l (N.G.head a) ≤ max (l (N.G.tail a) + N.τ a) (T0 a + y a / N.ν a)) ∧
                (∀ a, 0 < y a → max (l (N.G.tail a) + N.τ a) (T0 a + y a / N.ν a) ≤ l (N.G.head a)) ∧
                (∀ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧
                  max (l (N.G.tail a) + N.τ a) (T0 a + y a / N.ν a) ≤ l w) := by
            clear * - A_sum A_bdd A_max
            intro N hN T0 c M hM
            have hbdd := A_bdd N hN T0 c M hM
            choose B hB using hbdd
            have hst := hN.1
            have hν := hN.2.1
            have hτ := hN.2.2.1
            obtain ⟨L, hLc, hLT⟩ : ∃ L : ℝ, L ≤ c ∧ ∀ a, L ≤ T0 a := by
              obtain ⟨L, hL⟩ := (Set.finite_range T0).bddBelow
              exact ⟨min L c, min_le_right _ _, fun a => (min_le_left _ _).trans (hL ⟨a, rfl⟩)⟩
            have hex := fun n : ℕ => A_max N hN T0 c M hM (n + 1) L (by linarith [n.cast_nonneg (α := ℝ)]) hLc hLT
            choose l y hl1 hl2 hy he hp using hex
            have hKpos : ∀ n : ℕ, (0:ℝ) < n + 1 := fun n => by positivity
            have hy0 : ∀ n a, 0 ≤ y n a := by
              intro n a
              rw [hy]
              exact le_min (mul_nonneg (hν a).le (le_max_right _ _)) (mul_nonneg (hKpos n).le (le_max_right _ _))
            have hyz : ∀ n a, l n (N.G.head a) ≤ l n (N.G.tail a) + N.τ a → y n a = 0 := by
              intro n a h
              refine le_antisymm ?_ (hy0 n a)
              rw [hy]
              refine (min_le_right _ _).trans ?_
              rw [max_eq_right (by linarith)]; simp
            have hlB : ∀ n v, l n v ≤ B v := by
              intro n v
              refine hB v (l n) (y n) (hl1 n) (hy0 n) (fun a h => hyz n a (by linarith [hτ a]))
                (fun w hw => (he n w hw).le) ?_
              intro a h
              rw [hy] at h
              rcases min_le_iff.1 h with h | h
              · refine le_max_of_le_right ?_
                have h1 : N.ν a * (l n (N.G.head a) - T0 a) ≤ M :=
                  (mul_le_mul_of_nonneg_left (le_max_left _ _) (hν a).le).trans h
                have h2 : l n (N.G.head a) - T0 a ≤ M / N.ν a := by
                  rw [le_div_iff₀ (hν a)]; linarith
                linarith
              · refine le_max_of_le_left ?_
                have h0 := n.cast_nonneg (α := ℝ)
                have h1 : max (l n (N.G.head a) - l n (N.G.tail a) - N.τ a) 0 ≤ M := by
                  nlinarith [le_max_right (l n (N.G.head a) - l n (N.G.tail a) - N.τ a) 0]
                linarith [le_max_left (l n (N.G.head a) - l n (N.G.tail a) - N.τ a) 0]
            have hyle : ∀ n a, y n a ≤ N.ν a * max (l n (N.G.head a) - T0 a) 0 := by
              intro n a; rw [hy]; exact min_le_left _ _
            have hyB : ∀ n a, y n a ≤ N.ν a * max (B (N.G.head a) - T0 a) 0 := by
              intro n a
              refine (hyle n a).trans (mul_le_mul_of_nonneg_left (max_le_max ?_ le_rfl) (hν a).le)
              linarith [hlB n (N.G.head a)]
            have hlim : ∀ (f : ℕ → ℝ) (p q : ℝ), (∀ n, p ≤ f n ∧ f n ≤ q) →
                ∃ z, Filter.Tendsto f (Filter.hyperfilter ℕ : Filter ℕ) (nhds z) := by
              intro f p q hf
              obtain ⟨z, _, hz⟩ := isCompact_iff_ultrafilter_le_nhds.1 (isCompact_Icc (a := p) (b := q))
                ((Filter.hyperfilter ℕ).map f) (by
                  rw [Filter.le_principal_iff]
                  exact Filter.Eventually.of_forall (f := (Filter.hyperfilter ℕ : Filter ℕ)) hf)
              exact ⟨z, hz⟩
            have hl' := fun v => hlim (fun n => l n v) L (B v) fun n => ⟨hl2 n v, hlB n v⟩
            have hy' := fun a => hlim (fun n => y n a) 0 _ fun n => ⟨hy0 n a, hyB n a⟩
            choose l' hl' using hl'
            choose y' hy' using hy'
            have hne : (Filter.hyperfilter ℕ : Filter ℕ).NeBot := (Filter.hyperfilter ℕ).neBot
            have hy'0 : ∀ a, 0 ≤ y' a := fun a =>
              ge_of_tendsto (hy' a) (Filter.Eventually.of_forall fun n => hy0 n a)
            have hmaxT : ∀ a, Filter.Tendsto (fun n => N.ν a * max (l n (N.G.head a) - T0 a) 0)
                (Filter.hyperfilter ℕ : Filter ℕ) (nhds (N.ν a * max (l' (N.G.head a) - T0 a) 0)) := by
              intro a
              exact (((hl' (N.G.head a)).sub_const _).max tendsto_const_nhds).const_mul _
            have hy'le : ∀ a, y' a ≤ N.ν a * max (l' (N.G.head a) - T0 a) 0 := by
              intro a
              exact le_of_tendsto_of_tendsto' (hy' a) (hmaxT a) fun n => hyle n a
            have hdiv : ∀ a, T0 a ≤ l' (N.G.head a) → T0 a + y' a / N.ν a ≤ l' (N.G.head a) := by
              intro a h
              have h1 := hy'le a
              rw [max_eq_left (by linarith)] at h1
              have : y' a / N.ν a ≤ l' (N.G.head a) - T0 a := by
                rw [div_le_iff₀ (hν a)]; linarith
              linarith
            have hinT : ∀ w, Filter.Tendsto (fun n => inflow N.G (y n) w - outflow N.G (y n) w)
                (Filter.hyperfilter ℕ : Filter ℕ) (nhds (inflow N.G y' w - outflow N.G y' w)) := by
              intro w
              unfold inflow outflow
              exact (tendsto_finsetSum _ fun a _ => hy' a).sub (tendsto_finsetSum _ fun a _ => hy' a)
            have hnet : ∀ w, w ≠ N.G.s → inflow N.G y' w - outflow N.G y' w = if w = N.G.t then M else 0 := by
              intro w hw
              refine tendsto_nhds_unique (hinT w) ?_
              simp_rw [fun n => he n w hw]
              exact tendsto_const_nhds
            refine ⟨l', y', ?_, hy'0, ?_, ?_, ?_, ?_⟩
            · refine tendsto_nhds_unique (hl' N.G.s) ?_
              simp_rw [hl1]
              exact tendsto_const_nhds
            · intro v
              by_cases hv : v = N.G.s
              · have h0 := A_sum N.G Finset.univ y'
                simp only [Finset.mem_univ, if_true, sub_self, mul_zero, Finset.sum_const_zero] at h0
                rw [← Finset.add_sum_erase _ _ (Finset.mem_univ N.G.s)] at h0
                have h1 : ∑ w ∈ Finset.univ.erase N.G.s, (inflow N.G y' w - outflow N.G y' w) = M := by
                  rw [Finset.sum_congr rfl fun w hw => hnet w (Finset.ne_of_mem_erase hw), Finset.sum_ite_eq',
                    if_pos (Finset.mem_erase.2 ⟨Ne.symm hst, Finset.mem_univ _⟩)]
                rw [hv, if_pos rfl, if_neg hst]
                linarith
              · have := hnet v hv
                rw [if_neg hv]
                linarith
            · intro a
              by_cases h : l' (N.G.head a) ≤ l' (N.G.tail a) + N.τ a
              · exact le_max_of_le_left h
              push Not at h
              refine le_max_of_le_right ?_
              obtain ⟨δ, hδ0, hδ⟩ : ∃ δ, 0 < δ ∧ δ < l' (N.G.head a) - l' (N.G.tail a) - N.τ a :=
                exists_between (by linarith)
              have hd : Filter.Tendsto (fun n => l n (N.G.head a) - l n (N.G.tail a) - N.τ a)
                  (Filter.hyperfilter ℕ : Filter ℕ) (nhds (l' (N.G.head a) - l' (N.G.tail a) - N.τ a)) :=
                ((hl' _).sub (hl' _)).sub_const _
              have hev1 := hd.eventually (lt_mem_nhds hδ)
              have hev2 : ∀ᶠ n : ℕ in (Filter.hyperfilter ℕ : Filter ℕ),
                  N.ν a * max (B (N.G.head a) - T0 a) 0 ≤ ((n:ℝ) + 1) * δ := by
                have : ∀ᶠ n : ℕ in Filter.atTop, N.ν a * max (B (N.G.head a) - T0 a) 0 ≤ ((n:ℝ) + 1) * δ := by
                  obtain ⟨m, hm⟩ := exists_nat_ge (N.ν a * max (B (N.G.head a) - T0 a) 0 / δ)
                  filter_upwards [Filter.eventually_ge_atTop m] with n hn
                  rw [div_le_iff₀ hδ0] at hm
                  have : (m:ℝ) ≤ n := by exact_mod_cast hn
                  nlinarith
                rw [← Nat.cofinite_eq_atTop] at this
                exact this.filter_mono Filter.hyperfilter_le_cofinite
              have heq : y' a = N.ν a * max (l' (N.G.head a) - T0 a) 0 := by
                refine tendsto_nhds_unique (hy' a) ((hmaxT a).congr' ?_)
                filter_upwards [hev1, hev2] with n h1 h2
                rw [hy n a, min_eq_left]
                calc _ ≤ N.ν a * max (B (N.G.head a) - T0 a) 0 :=
                      mul_le_mul_of_nonneg_left (max_le_max (by linarith [hlB n (N.G.head a)]) le_rfl) (hν a).le
                  _ ≤ ((n:ℝ) + 1) * δ := h2
                  _ ≤ _ := mul_le_mul_of_nonneg_left (h1.le.trans (le_max_left _ _)) (hKpos n).le
              rw [heq, mul_div_cancel_left₀ _ (hν a).ne']
              linarith [le_max_left (l' (N.G.head a) - T0 a) 0]
            · intro a ha
              have hev := (hy' a).eventually (lt_mem_nhds ha)
              refine max_le ?_ (hdiv a ?_)
              · refine le_of_tendsto_of_tendsto ((hl' (N.G.tail a)).add_const (N.τ a)) (hl' (N.G.head a)) ?_
                filter_upwards [hev] with n hn
                by_contra hcon
                push Not at hcon
                exact hn.ne' (hyz n a hcon.le)
              · refine ge_of_tendsto (hl' (N.G.head a)) ?_
                filter_upwards [hev] with n hn
                by_contra hcon
                push Not at hcon
                have := hyle n a
                rw [max_eq_right (by linarith)] at this
                linarith
            · intro w hw
              obtain ⟨a, ha, hle⟩ : ∃ a, N.G.head a = w ∧ max (l' (N.G.tail a) + N.τ a) (T0 a) ≤ l' w := by
                by_contra hcon
                push Not at hcon
                have hev : ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ), ∀ a, N.G.head a = w →
                    l n w < max (l n (N.G.tail a) + N.τ a) (T0 a) := by
                  rw [Filter.eventually_all]
                  intro a
                  by_cases ha : N.G.head a = w
                  · have h1 : Filter.Tendsto (fun n => max (l n (N.G.tail a) + N.τ a) (T0 a))
                        (Filter.hyperfilter ℕ : Filter ℕ) (nhds (max (l' (N.G.tail a) + N.τ a) (T0 a))) :=
                      ((hl' _).add_const _).max tendsto_const_nhds
                    filter_upwards [(hl' w).eventually_lt h1 (hcon a ha)] with n hn _ using hn
                  · exact Filter.Eventually.of_forall fun n h => absurd h ha
                obtain ⟨n, hn⟩ := hev.exists
                obtain ⟨a, ha, hle⟩ := hp n w hw
                exact absurd hle (not_le.2 (hn a ha))
              refine ⟨a, ha, max_le ((le_max_left _ _).trans hle) ?_⟩
              have := hdiv a (by rw [ha]; exact (le_max_right _ _).trans hle)
              rwa [ha] at this
          have wf0 : ∀ (N : QNet) (_ : N.Standing) (l : N.G.V → ℝ),
              WellFounded (fun v w : N.G.V => ∃ a, N.G.tail a = v ∧ N.G.head a = w ∧ l v + N.τ a ≤ l w) := by
            clear * -
            intro N hN l
            have hac := hN.2.2.2.1
            have hτ := hN.2.2.1
            have key : ∀ v w : N.G.V, Relation.TransGen (fun v w : N.G.V => ∃ a, N.G.tail a = v ∧ N.G.head a = w ∧ l v + N.τ a ≤ l w) v w →
                l v ≤ l w ∧ (l w ≤ l v → Relation.TransGen (Adj (subNet N.G (Finset.univ.filter fun a => N.τ a = 0))) v w) := by
              intro v w h
              induction h with
              | single h =>
                obtain ⟨a, h1, h2, h3⟩ := h
                refine ⟨by linarith [hτ a], fun h4 => Relation.TransGen.single ?_⟩
                have : N.τ a = 0 := by linarith [hτ a]
                exact ⟨⟨a, by simp [this]⟩, h1, h2⟩
              | tail _ h ih =>
                obtain ⟨a, h1, h2, h3⟩ := h
                have := hτ a
                refine ⟨by linarith [ih.1], fun h4 => ?_⟩
                have h5 : N.τ a = 0 := by linarith [ih.1]
                exact Relation.TransGen.tail (ih.2 (by linarith)) ⟨⟨a, by simp [h5]⟩, h1, h2⟩
            have hirr : ∀ v, ¬ Relation.TransGen (fun v w : N.G.V => ∃ a, N.G.tail a = v ∧ N.G.head a = w ∧ l v + N.τ a ≤ l w) v v := by
              intro v h
              exact hac v ((key v v h).2 le_rfl)
            have hwf : WellFounded (Relation.TransGen (fun v w : N.G.V => ∃ a, N.G.tail a = v ∧ N.G.head a = w ∧ l v + N.τ a ≤ l w)) := by
              have : Std.Irrefl (Relation.TransGen (fun v w : N.G.V => ∃ a, N.G.tail a = v ∧ N.G.head a = w ∧ l v + N.τ a ≤ l w)) := ⟨hirr⟩
              exact Finite.wellFounded_of_trans_of_irrefl _
            exact Subrelation.wf (fun h => Relation.TransGen.single h) hwf
          have B_flowsum : ∀ (G : Net) (y : G.A → ℝ) (S : Finset G.V),
              ∑ v ∈ S, (outflow G y v - inflow G y v) =
                ∑ b, ((if G.tail b ∈ S then y b else 0) - (if G.head b ∈ S then y b else 0)) := by
            clear * -
            intro G y S
            simp only [outflow, inflow, Finset.sum_sub_distrib, Finset.sum_filter]
            congr 1
            · rw [Finset.sum_comm]
              simp
            · rw [Finset.sum_comm]
              simp
          have cut_bound : ∀ (N : QNet) (_ : N.Standing) (l : N.G.V → ℝ) (y : N.G.A → ℝ) (M : ℝ)
              (_ : 0 ≤ M) (_ : ∀ a, 0 ≤ y a)
              (_ : ∀ v, outflow N.G y v - inflow N.G y v =
                  (if v = N.G.s then M else 0) - (if v = N.G.t then M else 0))
              (_ : ∀ a, 0 < y a → l (N.G.tail a) + N.τ a ≤ l (N.G.head a)), ∀ a, y a ≤ M := by
            clear * - wf0 B_flowsum
            classical
            intro N hN l y M hM hy hnet hact a
            by_cases ha : 0 < y a
            swap
            · linarith
            have hwf := wf0 N hN l
            set R := (fun v w : N.G.V => ∃ a, N.G.tail a = v ∧ N.G.head a = w ∧ l v + N.τ a ≤ l w) with hR
            set S : Finset N.G.V := Finset.univ.filter (fun u => Relation.ReflTransGen R u (N.G.tail a)) with hS
            have hmem : ∀ u, u ∈ S ↔ Relation.ReflTransGen R u (N.G.tail a) := by
              intro u; simp [hS]
            have harc : ∀ b, 0 < y b → R (N.G.tail b) (N.G.head b) := fun b hb => ⟨b, rfl, rfl, hact b hb⟩
            have hta : N.G.tail a ∈ S := (hmem _).2 Relation.ReflTransGen.refl
            have hha : N.G.head a ∉ S := by
              intro h
              have h1 := (hmem _).1 h
              have h2 : Relation.TransGen R (N.G.tail a) (N.G.tail a) := Relation.TransGen.head' (harc a ha) h1
              have hwf' := hwf.transGen
              exact hwf'.asymmetric _ _ h2 h2
            have hsum := B_flowsum N.G y S
            have hterm : ∀ b, 0 ≤ (if N.G.tail b ∈ S then y b else 0) - (if N.G.head b ∈ S then y b else 0) := by
              intro b
              by_cases hb : 0 < y b
              · by_cases h1 : N.G.head b ∈ S
                · have h2 : N.G.tail b ∈ S := (hmem _).2 (Relation.ReflTransGen.head (harc b hb) ((hmem _).1 h1))
                  simp [h1, h2]
                · have := hy b
                  simp only [h1, if_false]
                  split_ifs <;> linarith
              · have : y b = 0 := le_antisymm (not_lt.1 hb) (hy b)
                simp [this]
            have hle : y a ≤ ∑ b, ((if N.G.tail b ∈ S then y b else 0) - (if N.G.head b ∈ S then y b else 0)) := by
              have := Finset.single_le_sum (f := fun b => ((if N.G.tail b ∈ S then y b else 0) - (if N.G.head b ∈ S then y b else 0))) (fun b _ => hterm b) (Finset.mem_univ a)
              simpa [hta, hha] using this
            have hr : ∑ v ∈ S, (outflow N.G y v - inflow N.G y v) ≤ M := by
              simp only [hnet, Finset.sum_sub_distrib, Finset.sum_ite_eq']
              split_ifs <;> linarith
            linarith
          have B_growth : ∀ (N : QNet) (_ : N.Standing) (l l' : N.G.V → ℝ) (T y : N.G.A → ℝ) (D : ℝ)
              (_ : ∀ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ T a ≤ l w)
              (_ : ∀ a, l (N.G.tail a) + N.τ a ≤ T a)
              (_ : ∀ a, l' (N.G.head a) ≤ max (l' (N.G.tail a) + N.τ a) (T a + y a / N.ν a))
              (_ : l' N.G.s - l N.G.s ≤ D) (_ : ∀ a, y a / N.ν a ≤ D), ∀ w, l' w - l w ≤ D := by
            clear * - wf0
            intro N hN l l' T y D hpred hT hl' hs hy w
            have hwf := wf0 N hN l
            induction w using hwf.induction with
            | _ w ih =>
              by_cases hw : w = N.G.s
              · rw [hw]; exact hs
              · obtain ⟨a, rfl, h1⟩ := hpred w hw
                have h2 := ih (N.G.tail a) ⟨a, rfl, rfl, by linarith [hT a]⟩
                have h3 := hl' a
                rcases le_max_iff.1 h3 with h4 | h4
                · linarith [hT a]
                · linarith [hy a]
          have B_flow_add : ∀ (G : Net) (x y : G.A → ℝ) (v : G.V),
              outflow G (fun a => x a + y a) v - inflow G (fun a => x a + y a) v =
                (outflow G x v - inflow G x v) + (outflow G y v - inflow G y v) := by
            clear * -
            intro G x y v
            simp only [outflow, inflow, Finset.sum_add_distrib]
            ring
          have disc : ∀ (N : QNet) (_ : N.Standing) (X : ℝ → ℝ) (_ : Monotone X) (_ : X 0 = 0)
              (l0 : N.G.V → ℝ)
              (_ : ∀ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l0 (N.G.tail a) + N.τ a ≤ l0 w),
              ∃ (C : ℝ), 0 ≤ C ∧ ∀ h : ℝ, 0 < h →
                ∃ (l : ℕ → N.G.V → ℝ) (x T : ℕ → N.G.A → ℝ),
                  l 0 = l0 ∧ (∀ a, x 0 a = 0) ∧ (∀ k : ℕ, l k N.G.s = k * h + l0 N.G.s) ∧
                  (∀ k a, l k (N.G.head a) ≤ T k a) ∧
                  (∀ k w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l k w = T k a) ∧
                  (∀ (k : ℕ) v, outflow N.G (x k) v - inflow N.G (x k) v =
                    (if v = N.G.s then X (k * h) else 0) - (if v = N.G.t then X (k * h) else 0)) ∧
                  (∀ (k : ℕ) v, 0 ≤ l (k+1) v - l k v ∧
                    l (k+1) v - l k v ≤ C * (h + X ((k+1 : ℕ) * h) - X (k * h))) ∧
                  (∀ (k : ℕ) a, 0 ≤ x (k+1) a - x k a ∧
                    x (k+1) a - x k a ≤ X ((k+1 : ℕ) * h) - X (k * h)) ∧
                  (∀ k a, x k a < x (k+1) a → l (k+1) (N.G.head a) = T (k+1) a) ∧
                  (∀ a, T 0 a = max (l 0 (N.G.head a)) (l 0 (N.G.tail a) + N.τ a)) ∧
                  (∀ k a, T (k+1) a = max (l (k+1) (N.G.tail a) + N.τ a)
                    (T k a + (x (k+1) a - x k a) / N.ν a)) := by
            clear * - step_exists cut_bound B_growth B_flow_add
            intro N hN X hX hX0 l0 hl0p
            have hν := hN.2.1
            have hC : 0 ≤ ∑ a, 1 / N.ν a := Finset.sum_nonneg (fun a _ => (one_div_pos.2 (hν a)).le)
            refine ⟨1 + ∑ a, 1 / N.ν a, by linarith, ?_⟩
            intro h hh
            have hM : ∀ k : ℕ, 0 ≤ X ((k + 1 : ℕ) * h) - X (k * h) := by
              intro k
              have : X (k * h) ≤ X ((k + 1 : ℕ) * h) := by
                apply hX
                apply mul_le_mul_of_nonneg_right _ hh.le
                exact_mod_cast Nat.le_succ k
              linarith
            have hstep := fun (k : ℕ) (T0 : N.G.A → ℝ) => step_exists N hN T0 (((k + 1 : ℕ) * h) + l0 N.G.s) _ (hM k)
            choose L Y hLs hY hnet hL1 hL2 hL3 using hstep
            obtain ⟨T, hT0, hTs⟩ : ∃ T : ℕ → N.G.A → ℝ, (T 0 = fun a => max (l0 (N.G.head a)) (l0 (N.G.tail a) + N.τ a)) ∧
                ∀ k, T (k + 1) = fun a => max (L k (T k) (N.G.tail a) + N.τ a) (T k a + Y k (T k) a / N.ν a) :=
              ⟨fun k => Nat.rec (fun a => max (l0 (N.G.head a)) (l0 (N.G.tail a) + N.τ a)) (fun k Tk => fun a => max (L k Tk (N.G.tail a) + N.τ a) (Tk a + Y k Tk a / N.ν a)) k, rfl, fun k => rfl⟩
            obtain ⟨l, hl0, hls⟩ : ∃ l : ℕ → N.G.V → ℝ, l 0 = l0 ∧ ∀ k, l (k + 1) = L k (T k) :=
              ⟨fun k => Nat.rec l0 (fun k _ => L k (T k)) k, rfl, fun k => rfl⟩
            obtain ⟨x, hx0, hxs⟩ : ∃ x : ℕ → N.G.A → ℝ, (∀ a, x 0 a = 0) ∧ ∀ k, x (k + 1) = fun a => x k a + Y k (T k) a :=
              ⟨fun k => Nat.rec (fun _ => 0) (fun k xk => fun a => xk a + Y k (T k) a) k, fun _ => rfl, fun k => rfl⟩
            have hle : ∀ k a, l k (N.G.head a) ≤ T k a := by
              intro k a
              cases k with
              | zero => rw [hl0, hT0]; exact le_max_left _ _
              | succ k => rw [hls, hTs]; exact hL1 k (T k) a
            have hpred : ∀ k w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l k w = T k a := by
              intro k w hw
              cases k with
              | zero =>
                obtain ⟨a, rfl, h1⟩ := hl0p w hw
                refine ⟨a, rfl, ?_⟩
                rw [hl0, hT0]; exact (max_eq_left h1).symm
              | succ k =>
                obtain ⟨a, rfl, h1⟩ := hL3 k (T k) w hw
                refine ⟨a, rfl, le_antisymm (hle _ _) ?_⟩
                rw [hls, hTs]; exact h1
            have hTge : ∀ k a, l k (N.G.tail a) + N.τ a ≤ T k a := by
              intro k a
              cases k with
              | zero => rw [hl0, hT0]; exact le_max_right _ _
              | succ k => rw [hls, hTs]; exact le_max_left _ _
            have hYM : ∀ k a, Y k (T k) a ≤ X ((k + 1 : ℕ) * h) - X (k * h) := by
              intro k a
              exact cut_bound N hN (L k (T k)) (Y k (T k)) _ (hM k) (hY k (T k)) (hnet k (T k))
                (fun a ha => (le_max_left _ _).trans (hL2 k (T k) a ha)) a
            have hlsrc : ∀ k : ℕ, l k N.G.s = k * h + l0 N.G.s := by
              intro k
              cases k with
              | zero => rw [hl0]; simp
              | succ k => rw [hls, hLs]
            refine ⟨l, x, T, hl0, hx0, hlsrc, hle, hpred, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro k v
              induction k with
              | zero =>
                have : x 0 = fun _ => 0 := funext hx0
                rw [this]
                simp [outflow, inflow, hX0]
              | succ k ih =>
                rw [hxs, B_flow_add, ih, hnet]
                split_ifs <;> ring
            · intro k v
              constructor
              · by_cases hv : v = N.G.s
                · rw [hv, hlsrc, hlsrc]
                  push_cast
                  nlinarith
                · obtain ⟨a, rfl, h1⟩ := hpred (k + 1) v hv
                  have h2 := hle k a
                  have h3 : T k a ≤ T (k + 1) a := by
                    rw [hTs]
                    refine le_trans ?_ (le_max_right _ _)
                    have := div_nonneg (hY k (T k) a) (hν a).le
                    linarith
                  linarith
              · have hMk := hM k
                have := B_growth N hN (l k) (l (k + 1)) (T k) (Y k (T k))
                  ((1 + ∑ a, 1 / N.ν a) * (h + (X ((k + 1 : ℕ) * h) - X (k * h))))
                  (fun w hw => by
                    obtain ⟨a, h1, h2⟩ := hpred k w hw
                    exact ⟨a, h1, h2.ge⟩)
                  (hTge k) (fun a => by rw [hls]; exact hL1 k (T k) a)
                  (by
                    rw [hlsrc, hlsrc]
                    push_cast at hMk ⊢
                    nlinarith [mul_nonneg hC hh.le, mul_nonneg hC hMk])
                  (fun a => by
                    have h1 : 1 / N.ν a ≤ ∑ a, 1 / N.ν a :=
                      Finset.single_le_sum (f := fun a => 1 / N.ν a) (fun a _ => (one_div_pos.2 (hν a)).le) (Finset.mem_univ a)
                    have h2 : Y k (T k) a / N.ν a = Y k (T k) a * (1 / N.ν a) := by ring
                    rw [h2]
                    have h3 : Y k (T k) a * (1 / N.ν a) ≤ (X ((k + 1 : ℕ) * h) - X (k * h)) * ∑ a, 1 / N.ν a :=
                      mul_le_mul (hYM k a) h1 (one_div_pos.2 (hν a)).le hMk
                    nlinarith [mul_nonneg hC hh.le])
                  v
                rw [← add_sub_assoc] at this
                exact this
            · intro k a
              rw [hxs]
              simp only [add_sub_cancel_left]
              exact ⟨hY k (T k) a, hYM k a⟩
            · intro k a hlt
              rw [hxs] at hlt
              refine le_antisymm (hle _ _) ?_
              rw [hls, hTs]
              exact hL2 k (T k) a (by simpa using hlt)
            · intro a
              rw [hT0, hl0]
            · intro k a
              rw [hTs, hls, hxs]
              simp only [add_sub_cancel_left]
          have C_ulim : ∀ (f : ℕ → ℝ) (A B : ℝ), (∀ n, A ≤ f n ∧ f n ≤ B) →
              ∃ L, Filter.Tendsto f (Filter.hyperfilter ℕ : Filter ℕ) (nhds L) := by
            clear * -
            intro f A B h
            have h1 := (isCompact_Icc (a := A) (b := B)).ultrafilter_le_nhds
              ((Filter.hyperfilter ℕ).map f) (by
                rw [Filter.le_principal_iff]
                exact Filter.mem_map.2 (Filter.Eventually.of_forall (fun n => h n)))
            obtain ⟨L, -, hL⟩ := h1
            exact ⟨L, hL⟩
          have C_move : ∀ (f : ℕ → ℝ → ℝ) (h θn : ℕ → ℝ) (X : ℝ → ℝ) (C θ L : ℝ) (_ : Continuous X)
              (_ : ∀ n α β, α ≤ β → 0 ≤ f n β - f n α ∧
                f n β - f n α ≤ C * (β - α + h n + X β - X (α - h n)))
              (_ : Filter.Tendsto h (Filter.hyperfilter ℕ : Filter ℕ) (nhds 0))
              (_ : Filter.Tendsto θn (Filter.hyperfilter ℕ : Filter ℕ) (nhds θ))
              (_ : Filter.Tendsto (fun n => f n θ) (Filter.hyperfilter ℕ : Filter ℕ) (nhds L)),
              Filter.Tendsto (fun n => f n (θn n)) (Filter.hyperfilter ℕ : Filter ℕ) (nhds L) := by
            clear * -
            intro f h θn X C θ L hX hf hh hθ hL
            have hE : Filter.Tendsto (fun n => C * (|θn n - θ| + h n + X (max (θn n) θ)
                - X (min (θn n) θ - h n))) (Filter.hyperfilter ℕ : Filter ℕ) (nhds 0) := by
              have h1 : Filter.Tendsto (fun n => |θn n - θ|) (Filter.hyperfilter ℕ : Filter ℕ) (nhds 0) := by
                have := (hθ.sub_const θ).abs
                simpa using this
              have h2 : Filter.Tendsto (fun n => X (max (θn n) θ)) (Filter.hyperfilter ℕ : Filter ℕ)
                  (nhds (X θ)) := by
                have := (hX.tendsto (max θ θ)).comp (hθ.max (tendsto_const_nhds (x := θ)))
                simpa [Function.comp_def] using this
              have h3 : Filter.Tendsto (fun n => X (min (θn n) θ - h n)) (Filter.hyperfilter ℕ : Filter ℕ)
                  (nhds (X θ)) := by
                have := (hX.tendsto (min θ θ - 0)).comp ((hθ.min (tendsto_const_nhds (x := θ))).sub hh)
                simpa [Function.comp_def] using this
              have := ((((h1.add hh).add h2).sub h3).const_mul C)
              simpa using this
            have hd : Filter.Tendsto (fun n => f n (θn n) - f n θ) (Filter.hyperfilter ℕ : Filter ℕ)
                (nhds 0) := by
              apply squeeze_zero_norm _ hE
              intro n
              rw [Real.norm_eq_abs]
              rcases le_total (θn n) θ with hc | hc
              · have := hf n _ _ hc
                rw [max_eq_right hc, min_eq_left hc, abs_of_nonpos (by linarith : f n (θn n) - f n θ ≤ 0),
                  abs_of_nonpos (by linarith : θn n - θ ≤ 0)]
                have e : C * (-(θn n - θ) + h n + X θ - X (θn n - h n)) =
                  C * (θ - θn n + h n + X θ - X (θn n - h n)) := by ring
                linarith [this.2]
              · have := hf n _ _ hc
                rw [max_eq_left hc, min_eq_right hc, abs_of_nonneg (by linarith : 0 ≤ f n (θn n) - f n θ),
                  abs_of_nonneg (by linarith : 0 ≤ θn n - θ)]
                exact this.2
            have := hd.add hL
            simpa using this
          have C_tel : ∀ (N : QNet) (_ : N.Standing) (X : ℝ → ℝ) (C h : ℝ)
              (l : ℕ → N.G.V → ℝ) (x T : ℕ → N.G.A → ℝ)
              (_ : ∀ (k : ℕ) v, 0 ≤ l (k+1) v - l k v ∧
                    l (k+1) v - l k v ≤ C * (h + X ((k+1 : ℕ) * h) - X (k * h)))
              (_ : ∀ (k : ℕ) a, 0 ≤ x (k+1) a - x k a ∧
                    x (k+1) a - x k a ≤ X ((k+1 : ℕ) * h) - X (k * h))
              (_ : ∀ k a, x k a < x (k+1) a → l (k+1) (N.G.head a) = T (k+1) a)
              (_ : ∀ a, T 0 a = max (l 0 (N.G.head a)) (l 0 (N.G.tail a) + N.τ a))
              (_ : ∀ k a, T (k+1) a = max (l (k+1) (N.G.tail a) + N.τ a)
                    (T k a + (x (k+1) a - x k a) / N.ν a))
              (_ : ∀ k a, l k (N.G.head a) ≤ T k a),
              (∀ (j k : ℕ) v, j ≤ k → 0 ≤ l k v - l j v ∧
                l k v - l j v ≤ C * (k * h - j * h + X (k * h) - X (j * h))) ∧
              (∀ (j k : ℕ) a, j ≤ k → 0 ≤ x k a - x j a ∧ x k a - x j a ≤ X (k * h) - X (j * h)) ∧
              (∀ (j k : ℕ) a, j ≤ k → x j a < x k a → ∃ i, j < i ∧ i ≤ k ∧ l i (N.G.head a) = T i a) ∧
              (∀ (j k : ℕ) a, j ≤ k → T j a + (x k a - x j a) / N.ν a ≤ T k a) ∧
              (∀ (j k : ℕ) a, j ≤ k → T k a ≤
                max (l k (N.G.tail a) + N.τ a) (T j a) + (x k a - x j a) / N.ν a) ∧
              (∀ k a, T k a = max (l k (N.G.head a)) (l k (N.G.tail a) + N.τ a)) := by
            clear * -
            intro N hN X C h l x T h1 h2 h3 h4 h5 h6
            have f1 : ∀ (j k : ℕ) v, j ≤ k → 0 ≤ l k v - l j v ∧
                l k v - l j v ≤ C * (k * h - j * h + X (k * h) - X (j * h)) := by
              intro j k v hjk
              induction k, hjk using Nat.le_induction with
              | base => simp
              | succ k hk ih =>
                have := h1 k v
                push_cast at this ⊢
                constructor
                · linarith [this.1, ih.1]
                · nlinarith [this.2, ih.2]
            refine ⟨f1, ?_, ?_, ?_, ?_, ?_⟩
            · intro j k v hjk
              induction k, hjk using Nat.le_induction with
              | base => simp
              | succ k hk ih =>
                have := h2 k v
                constructor
                · linarith [this.1, ih.1]
                · linarith [this.2, ih.2]
            · intro j k a hjk
              induction k, hjk using Nat.le_induction with
              | base => intro h; exact absurd h (lt_irrefl _)
              | succ k hk ih =>
                intro hlt
                by_cases hc : x j a < x k a
                · obtain ⟨i, hi1, hi2, hi3⟩ := ih hc
                  exact ⟨i, hi1, by omega, hi3⟩
                · exact ⟨k+1, by omega, le_refl _, h3 k a (by push Not at hc; linarith)⟩
            · intro j k a hjk
              induction k, hjk using Nat.le_induction with
              | base => simp
              | succ k hk ih =>
                rw [h5]
                refine le_trans ?_ (le_max_right _ _)
                have e : (x (k+1) a - x j a) / N.ν a = (x k a - x j a) / N.ν a
                  + (x (k+1) a - x k a) / N.ν a := by ring
                rw [e]; linarith
            · intro j k a hjk
              have xmono : ∀ j k, j ≤ k → 0 ≤ x k a - x j a := by
                intro j k h
                induction k, h using Nat.le_induction with
                | base => simp
                | succ k hk ih => linarith [(h2 k a).1]
              induction k, hjk using Nat.le_induction with
              | base => simp
              | succ k hk ih =>
                rw [h5]
                have hm : l k (N.G.tail a) + N.τ a ≤ l (k+1) (N.G.tail a) + N.τ a :=
                  by linarith [(h1 k (N.G.tail a)).1]
                have hx : 0 ≤ (x (k+1) a - x j a) / N.ν a :=
                  div_nonneg (xmono j (k+1) (by omega)) (hN.2.1 a).le
                apply max_le
                · exact (le_max_left _ _).trans (le_add_of_nonneg_right hx)
                · calc
                    T k a + (x (k+1) a - x k a) / N.ν a
                        ≤ (max (l k (N.G.tail a) + N.τ a) (T j a) + (x k a - x j a) / N.ν a)
                            + (x (k+1) a - x k a) / N.ν a := add_le_add ih le_rfl
                    _ ≤ (max (l (k+1) (N.G.tail a) + N.τ a) (T j a) + (x k a - x j a) / N.ν a)
                            + (x (k+1) a - x k a) / N.ν a :=
                      add_le_add (add_le_add (max_le_max hm le_rfl) le_rfl) le_rfl
                    _ = _ := by ring
            · intro k a
              induction k with
              | zero => exact h4 a
              | succ k ih =>
                by_cases hp : x k a < x (k+1) a
                · have he := h3 k a hp
                  apply le_antisymm
                  · rw [← he]; exact le_max_left _ _
                  · apply max_le he.le
                    rw [h5]; exact le_max_left _ _
                · have hz : x (k+1) a - x k a = 0 := by linarith [(h2 k a).1]
                  apply le_antisymm
                  · rw [h5, hz, zero_div, add_zero, ih]
                    apply max_le (le_max_right _ _)
                    apply max_le
                    · exact (by linarith [(h1 k (N.G.head a)).1] : l k (N.G.head a) ≤ l (k+1) (N.G.head a)).trans (le_max_left _ _)
                    · exact (by linarith [(h1 k (N.G.tail a)).1] : l k (N.G.tail a) + N.τ a ≤ l (k+1) (N.G.tail a) + N.τ a).trans (le_max_right _ _)
                  · apply max_le (h6 (k+1) a)
                    rw [h5]; exact le_max_left _ _
          have C_approx : ∀ (N : QNet) (_ : N.Standing) (X : ℝ → ℝ) (_ : Monotone X)
              (_ : ∀ θ ≤ 0, X θ = 0)
              (l0 : N.G.V → ℝ)
              (_ : ∀ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l0 (N.G.tail a) + N.τ a ≤ l0 w),
              ∃ (C : ℝ), 0 ≤ C ∧ ∀ h : ℝ, 0 < h →
                ∃ (tn : ℝ → ℝ) (l : ℝ → N.G.V → ℝ) (x T : ℝ → N.G.A → ℝ),
                (∀ θ, θ - h ≤ tn θ ∧ tn θ ≤ θ) ∧
                (∀ v, l 0 v = l0 v) ∧
                (∀ θ, l θ N.G.s = tn θ + l0 N.G.s) ∧ (∀ θ ≤ 0, ∀ a, x θ a = 0) ∧
                (∀ α β v, α ≤ β → 0 ≤ l β v - l α v ∧
                  l β v - l α v ≤ C * (β - α + h + X β - X (α - h))) ∧
                (∀ α β a, α ≤ β → 0 ≤ x β a - x α a ∧ x β a - x α a ≤ X β - X (α - h)) ∧
                (∀ θ v, outflow N.G (x θ) v - inflow N.G (x θ) v =
                  (if v = N.G.s then X (tn θ) else 0) - (if v = N.G.t then X (tn θ) else 0)) ∧
                (∀ θ a, l θ (N.G.head a) ≤ T θ a) ∧
                (∀ θ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l θ w = T θ a) ∧
                (∀ α β a, α ≤ β → x α a < x β a → ∃ θ ∈ Set.Icc α β, l θ (N.G.head a) = T θ a) ∧
                (∀ α β a, α ≤ β → T α a + (x β a - x α a) / N.ν a ≤ T β a) ∧
                (∀ α β a, 0 ≤ α → α ≤ β → T β a ≤
                  max (l β (N.G.tail a) + N.τ a) (T α a) + (x β a - x α a) / N.ν a) ∧
                (∀ θ a, T θ a = max (l θ (N.G.head a)) (l θ (N.G.tail a) + N.τ a)) := by
            clear * - disc C_tel
            intro N hN X hX hX0 l0 hl0p
            obtain ⟨C, hC, H⟩ := disc N hN X hX (hX0 0 le_rfl) l0 hl0p
            refine ⟨C + 1, by linarith, ?_⟩
            intro h hh
            obtain ⟨l, x, T, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := H h hh
            obtain ⟨f1, f2, f3, f4, f5, f6⟩ := C_tel N hN X C h l x T e7 e8 e9 e10 e11 e4
            obtain ⟨K, hK⟩ : ∃ K : ℝ → ℕ, K = fun θ => ⌊θ / h⌋₊ := ⟨_, rfl⟩
            have K0 : ∀ θ ≤ 0, K θ = 0 := by
              intro θ hθ
              rw [hK]
              exact Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg hθ hh.le)
            have Kle : ∀ θ, 0 ≤ θ → (K θ : ℝ) * h ≤ θ := by
              intro θ hθ
              have := Nat.floor_le (div_nonneg hθ hh.le)
              rw [le_div_iff₀ hh] at this
              rw [hK]; exact this
            have Klt : ∀ θ, θ < ((K θ : ℝ) + 1) * h := by
              intro θ
              have := Nat.lt_floor_add_one (θ / h)
              rw [div_lt_iff₀ hh] at this
              rw [hK]; exact this
            have Kmono : ∀ α β, α ≤ β → K α ≤ K β := by
              intro α β hab
              rw [hK]
              exact Nat.floor_le_floor (by gcongr)
            have Knat : ∀ i : ℕ, K ((i : ℝ) * h) = i := by
              intro i
              rw [hK]
              show ⌊(i : ℝ) * h / h⌋₊ = i
              rw [mul_div_assoc, div_self hh.ne', mul_one, Nat.floor_natCast]
            have tnb : ∀ θ, θ - h ≤ (K θ : ℝ) * h + min θ 0 ∧ (K θ : ℝ) * h + min θ 0 ≤ θ := by
              intro θ
              rcases le_total θ 0 with hc | hc
              · rw [K0 θ hc, min_eq_left hc]
                constructor <;> simp <;> linarith
              · rw [min_eq_right hc]
                have := Klt θ
                have := Kle θ hc
                constructor <;> linarith
            have XK : ∀ θ, X ((K θ : ℝ) * h) = X ((K θ : ℝ) * h + min θ 0) := by
              intro θ
              rcases le_total θ 0 with hc | hc
              · rw [K0 θ hc, min_eq_left hc, hX0 _ (by simp), hX0 _ (by simpa using hc)]
              · rw [min_eq_right hc, add_zero]
            have XK1 : ∀ θ, X ((K θ : ℝ) * h) ≤ X θ := by
              intro θ; rw [XK]; exact hX (tnb θ).2
            have XK2 : ∀ θ, X (θ - h) ≤ X ((K θ : ℝ) * h) := by
              intro θ; rw [XK]; exact hX (tnb θ).1
            have K00 := K0 0 le_rfl
            refine ⟨fun θ => (K θ : ℝ) * h + min θ 0, fun θ v => l (K θ) v + min θ 0,
              fun θ a => x (K θ) a, fun θ a => T (K θ) a + min θ 0, tnb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
              ?_, ?_, ?_⟩
            · intro v; simp [K00, e1]
            · intro θ; simp [e3]; ring
            · intro θ hθ a; simp [K0 θ hθ, e2]
            · intro α β v hab
              have g1 := f1 _ _ v (Kmono α β hab)
              have m1 : min α 0 ≤ min β 0 := min_le_min_right 0 hab
              have g2 := tnb α
              have g3 := tnb β
              have g4 := XK1 β
              have g5 := XK2 α
              refine ⟨by simp only []; linarith [g1.1], ?_⟩
              have Kc : (K α : ℝ) * h ≤ (K β : ℝ) * h := by
                have : (K α : ℝ) ≤ K β := by exact_mod_cast Kmono α β hab
                gcongr
              have Xc : X ((K α : ℝ) * h) ≤ X ((K β : ℝ) * h) := hX Kc
              have P : (K β : ℝ) * h - (K α : ℝ) * h + X ((K β : ℝ) * h) - X ((K α : ℝ) * h) + (min β 0 - min α 0)
                  ≤ β - α + h + X β - X (α - h) := by linarith
              have Q : C * ((K β : ℝ) * h - (K α : ℝ) * h + X ((K β : ℝ) * h) - X ((K α : ℝ) * h)) ≤
                  C * (β - α + h + X β - X (α - h)) := by
                apply mul_le_mul_of_nonneg_left _ hC
                linarith
              show l (K β) v + min β 0 - (l (K α) v + min α 0) ≤ _
              linarith [g1.2]
            · intro α β a hab
              have g1 := f2 _ _ a (Kmono α β hab)
              exact ⟨g1.1, by linarith [g1.2, XK1 β, XK2 α]⟩
            · intro θ v
              have := e6 (K θ) v
              rw [XK] at this
              exact this
            · intro θ a
              show _ + _ ≤ _ + _
              linarith [e4 (K θ) a]
            · intro θ w hw
              obtain ⟨a, ha, hl⟩ := e5 (K θ) w hw
              exact ⟨a, ha, by show _ + _ = _ + _; rw [hl]⟩
            · intro α β a hab hx
              obtain ⟨i, hi1, hi2, hi3⟩ := f3 _ _ a (Kmono α β hab) hx
              have hβ : 0 ≤ β := by
                by_contra hcon
                push Not at hcon
                rw [K0 β hcon.le] at hi2
                omega
              refine ⟨(i : ℝ) * h, ⟨?_, ?_⟩, ?_⟩
              · have := Klt α
                have c : (K α : ℝ) + 1 ≤ i := by exact_mod_cast hi1
                have : ((K α : ℝ) + 1) * h ≤ i * h := by gcongr
                linarith
              · have := Kle β hβ
                have c : (i : ℝ) ≤ K β := by exact_mod_cast hi2
                have : (i : ℝ) * h ≤ K β * h := by gcongr
                linarith
              · simp only [Knat]
                rw [hi3]
            · intro α β a hab
              have g1 := f4 _ _ a (Kmono _ _ hab)
              have m1 : min α 0 ≤ min β 0 := min_le_min_right 0 hab
              show T (K α) a + min α 0 + (x (K β) a - x (K α) a) / N.ν a
                ≤ T (K β) a + min β 0
              linarith
            · intro α β a hα hab
              have hβ := hα.trans hab
              simp only [min_eq_right hα, min_eq_right hβ, add_zero]
              exact f5 _ _ a (Kmono _ _ hab)
            · intro θ a
              dsimp only
              rw [f6]
              rw [show l (K θ) (N.G.tail a) + min θ 0 + N.τ a = (l (K θ) (N.G.tail a) + N.τ a) + min θ 0 by ring, max_add_add_right]
          have limit_exists : ∀ (N : QNet) (_ : N.Standing) (X : ℝ → ℝ) (_ : Monotone X)
              (_ : Continuous X) (_ : ∀ θ ≤ 0, X θ = 0)
              (l0 : N.G.V → ℝ)
              (_ : ∀ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l0 (N.G.tail a) + N.τ a ≤ l0 w),
              ∃ (C : ℝ) (l : ℝ → N.G.V → ℝ) (x T : ℝ → N.G.A → ℝ), 0 ≤ C ∧
                (l 0 = l0) ∧ (∀ θ, l θ N.G.s = θ + l0 N.G.s) ∧ (∀ θ ≤ 0, ∀ a, x θ a = 0) ∧
                (∀ α β v, α ≤ β → 0 ≤ l β v - l α v ∧ l β v - l α v ≤ C * (β - α + X β - X α)) ∧
                (∀ α β a, α ≤ β → 0 ≤ x β a - x α a ∧ x β a - x α a ≤ X β - X α) ∧
                (∀ θ v, outflow N.G (x θ) v - inflow N.G (x θ) v =
                  (if v = N.G.s then X θ else 0) - (if v = N.G.t then X θ else 0)) ∧
                (∀ θ a, l θ (N.G.head a) ≤ T θ a) ∧
                (∀ θ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l θ w = T θ a) ∧
                (∀ α β a, α ≤ β → x α a < x β a → ∃ θ ∈ Set.Icc α β, l θ (N.G.head a) = T θ a) ∧
                (∀ α β a, α ≤ β → T α a + (x β a - x α a) / N.ν a ≤ T β a) ∧
                (∀ α β a, 0 ≤ α → α ≤ β → T β a ≤
                  max (l β (N.G.tail a) + N.τ a) (T α a) + (x β a - x α a) / N.ν a) ∧
                (∀ θ a, T θ a = max (l θ (N.G.head a)) (l θ (N.G.tail a) + N.τ a)) := by
            clear * - C_approx C_ulim C_move
            intro N hN X hX hXc hX0 l0 hl0p
            obtain ⟨C, hC, H⟩ := C_approx N hN X hX hX0 l0 hl0p
            have hpos : ∀ n : ℕ, (0:ℝ) < 1 / ((n:ℝ) + 1) := fun n => by positivity
            choose tn l x T e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 using fun n : ℕ => H (1 / ((n:ℝ) + 1)) (hpos n)
            have hh : Filter.Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) (Filter.hyperfilter ℕ : Filter ℕ) (nhds 0) :=
              tendsto_one_div_add_atTop_nhds_zero_nat.mono_left Nat.hyperfilter_le_atTop
            have hle1 : ∀ n : ℕ, 1 / ((n:ℝ) + 1) ≤ 1 := fun n => by
              rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
            have hX00 : ∀ θ, 0 ≤ X θ := by
              intro θ
              rcases le_total θ 0 with hc | hc
              · rw [hX0 θ hc]
              · rw [← hX0 0 le_rfl]; exact hX hc
            have xb : ∀ n θ a, 0 ≤ x n θ a ∧ x n θ a ≤ X θ := by
              intro n θ a
              rcases le_total θ 0 with hc | hc
              · rw [e4 n θ hc a]; exact ⟨le_rfl, hX00 θ⟩
              · have := e6 n 0 θ a hc
                rw [e4 n 0 le_rfl a] at this
                have h3 := hX00 (0 - 1 / ((n:ℝ) + 1))
                exact ⟨by linarith [this.1], by linarith [this.2]⟩
            have lb : ∀ θ v, ∃ B, ∀ n, -B ≤ l n θ v ∧ l n θ v ≤ B := by
              intro θ v
              refine ⟨|l0 v| + C * (|θ| + 1 + X |θ|), ?_⟩
              intro n
              have a1 := neg_abs_le (l0 v)
              have a2 := le_abs_self (l0 v)
              have hp := hpos n
              have hl := hle1 n
              rcases le_total θ 0 with hc | hc
              · have := e5 n θ 0 v hc
                rw [e2] at this
                have h3 := hX00 (θ - 1 / ((n:ℝ) + 1))
                have h4 := hX00 |θ|
                have h5 : C * (0 - θ + 1 / ((n:ℝ) + 1) + X 0 - X (θ - 1 / ((n:ℝ) + 1))) ≤
                    C * (|θ| + 1 + X |θ|) := by
                  apply mul_le_mul_of_nonneg_left _ hC
                  rw [hX0 0 le_rfl, abs_of_nonpos hc] at *
                  linarith
                have h6 : 0 ≤ C * (|θ| + 1 + X |θ|) := by positivity
                constructor <;> linarith [this.1, this.2]
              · have := e5 n 0 θ v hc
                rw [e2] at this
                have h3 := hX00 (0 - 1 / ((n:ℝ) + 1))
                have h4 := hX00 |θ|
                have h5 : C * (θ - 0 + 1 / ((n:ℝ) + 1) + X θ - X (0 - 1 / ((n:ℝ) + 1))) ≤
                    C * (|θ| + 1 + X |θ|) := by
                  apply mul_le_mul_of_nonneg_left _ hC
                  rw [abs_of_nonneg hc] at *
                  linarith
                have h6 : 0 ≤ C * (|θ| + 1 + X |θ|) := by positivity
                constructor <;> linarith [this.1, this.2]
            have Ll : ∀ θ v, ∃ L, Filter.Tendsto (fun n => l n θ v) (Filter.hyperfilter ℕ : Filter ℕ) (nhds L) := by
              intro θ v
              obtain ⟨B, hB⟩ := lb θ v
              exact C_ulim _ _ _ hB
            have Lx : ∀ θ a, ∃ L, Filter.Tendsto (fun n => x n θ a) (Filter.hyperfilter ℕ : Filter ℕ) (nhds L) := by
              intro θ a
              exact C_ulim _ _ _ (fun n => xb n θ a)
            choose L hL using Ll
            choose Y hY using Lx
            let S : ℝ → N.G.A → ℝ := fun θ a => max (L θ (N.G.head a)) (L θ (N.G.tail a) + N.τ a)
            have hS : ∀ θ a, Filter.Tendsto (fun n => T n θ a) (Filter.hyperfilter ℕ : Filter ℕ) (nhds (S θ a)) := by
              intro θ a
              exact ((hL θ (N.G.head a)).max ((hL θ (N.G.tail a)).add_const (N.τ a))).congr (fun n => (e13 n θ a).symm)
            have mL : ∀ (θn : ℕ → ℝ) θ v, Filter.Tendsto θn (Filter.hyperfilter ℕ : Filter ℕ) (nhds θ) →
                Filter.Tendsto (fun n => l n (θn n) v) (Filter.hyperfilter ℕ : Filter ℕ) (nhds (L θ v)) := by
              intro θn θ v hθ
              exact C_move (fun n θ => l n θ v) (fun n : ℕ => 1 / ((n:ℝ) + 1)) θn X C θ (L θ v) hXc
                (fun n α β hab => e5 n α β v hab) hh hθ (hL θ v)
            have mY : ∀ (θn : ℕ → ℝ) θ a, Filter.Tendsto θn (Filter.hyperfilter ℕ : Filter ℕ) (nhds θ) →
                Filter.Tendsto (fun n => x n (θn n) a) (Filter.hyperfilter ℕ : Filter ℕ) (nhds (Y θ a)) := by
              intro θn θ a hθ
              exact C_move (fun n θ => x n θ a) (fun n : ℕ => 1 / ((n:ℝ) + 1)) θn X 1 θ (Y θ a) hXc
                (fun n α β hab => ⟨(e6 n α β a hab).1, by
                  have := (e6 n α β a hab).2
                  have := hpos n
                  linarith⟩) hh hθ (hY θ a)
            have tlim : ∀ θ, Filter.Tendsto (fun n => tn n θ) (Filter.hyperfilter ℕ : Filter ℕ) (nhds θ) := by
              intro θ
              refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => θ - 1 / ((n:ℝ) + 1))
                (h := fun _ => θ) ?_ tendsto_const_nhds (fun n => (e1 n θ).1) (fun n => (e1 n θ).2)
              simpa using hh.const_sub θ
            have Xt : ∀ θ, Filter.Tendsto (fun n => X (tn n θ)) (Filter.hyperfilter ℕ : Filter ℕ) (nhds (X θ)) :=
              fun θ => (hXc.tendsto θ).comp (tlim θ)
            have Xh : ∀ θ, Filter.Tendsto (fun n : ℕ => X (θ - 1 / ((n:ℝ) + 1)))
                (Filter.hyperfilter ℕ : Filter ℕ) (nhds (X θ)) := by
              intro θ
              have := (hXc.tendsto (θ - 0)).comp (hh.const_sub θ)
              simpa [Function.comp_def] using this
            have modL : ∀ α β v, α ≤ β → 0 ≤ L β v - L α v ∧ L β v - L α v ≤ C * (β - α + X β - X α) := by
              intro α β v hab
              constructor
              · exact ge_of_tendsto' ((hL β v).sub (hL α v)) (fun n => (e5 n α β v hab).1)
              · have r : Filter.Tendsto (fun n : ℕ => C * (β - α + 1 / ((n:ℝ) + 1) + X β
                    - X (α - 1 / ((n:ℝ) + 1)))) (Filter.hyperfilter ℕ : Filter ℕ)
                    (nhds (C * (β - α + 0 + X β - X α))) :=
                  (((hh.const_add (β - α)).add_const (X β)).sub (Xh α)).const_mul C
                rw [add_zero] at r
                exact le_of_tendsto_of_tendsto' ((hL β v).sub (hL α v)) r (fun n => (e5 n α β v hab).2)
            have modY : ∀ α β a, α ≤ β → 0 ≤ Y β a - Y α a ∧ Y β a - Y α a ≤ X β - X α := by
              intro α β a hab
              constructor
              · exact ge_of_tendsto' ((hY β a).sub (hY α a)) (fun n => (e6 n α β a hab).1)
              · exact le_of_tendsto_of_tendsto' ((hY β a).sub (hY α a)) ((Xh α).const_sub (X β))
                  (fun n => (e6 n α β a hab).2)
            have cpt : ∀ (p q : ℝ) (θn : ℕ → ℝ), (∀ n, p ≤ θn n ∧ θn n ≤ q) → ∃ θ, p ≤ θ ∧ θ ≤ q ∧
                Filter.Tendsto θn (Filter.hyperfilter ℕ : Filter ℕ) (nhds θ) := by
              intro p q θn hθ
              obtain ⟨θ, hlim⟩ := C_ulim θn p q hθ
              exact ⟨θ, ge_of_tendsto' hlim (fun n => (hθ n).1), le_of_tendsto' hlim (fun n => (hθ n).2), hlim⟩
            refine ⟨C, L, Y, S, hC, ?_, ?_, ?_, modL, modY, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
            · funext v
              exact tendsto_nhds_unique (hL 0 v) ((tendsto_const_nhds (x := l0 v)).congr (fun n => (e2 n v).symm))
            · intro θ
              exact tendsto_nhds_unique (hL θ N.G.s) (((tlim θ).add_const (l0 N.G.s)).congr (fun n => (e3 n θ).symm))
            · intro θ hθ a
              exact tendsto_nhds_unique (hY θ a)
                ((tendsto_const_nhds (x := (0:ℝ))).congr (fun n => (e4 n θ hθ a).symm))
            · intro θ v
              have r1 : Filter.Tendsto (fun n => outflow N.G (x n θ) v - inflow N.G (x n θ) v)
                  (Filter.hyperfilter ℕ : Filter ℕ) (nhds (outflow N.G (Y θ) v - inflow N.G (Y θ) v)) := by
                unfold outflow inflow
                exact (tendsto_finsetSum _ (fun a _ => hY θ a)).sub (tendsto_finsetSum _ (fun a _ => hY θ a))
              have r2 : Filter.Tendsto (fun n => (if v = N.G.s then X (tn n θ) else 0)
                  - (if v = N.G.t then X (tn n θ) else 0)) (Filter.hyperfilter ℕ : Filter ℕ)
                  (nhds ((if v = N.G.s then X θ else 0) - (if v = N.G.t then X θ else 0))) := by
                apply Filter.Tendsto.sub
                · split_ifs
                  · exact Xt θ
                  · exact tendsto_const_nhds
                · split_ifs
                  · exact Xt θ
                  · exact tendsto_const_nhds
              exact tendsto_nhds_unique r1 (r2.congr (fun n => (e7 n θ v).symm))
            · intro θ a
              exact le_of_tendsto_of_tendsto' (hL θ _) (hS θ a) (fun n => e8 n θ a)
            · intro θ w hw
              choose an ha1 ha2 using fun n => e9 n θ w hw
              have : ∃ a, ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ), an n = a := by
                have hf : ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ), ∃ a ∈ (Set.univ : Set N.G.A), an n = a :=
                  Filter.Eventually.of_forall (fun n => ⟨an n, trivial, rfl⟩)
                obtain ⟨a, -, ha⟩ := (Ultrafilter.eventually_exists_mem_iff (Set.finite_univ)).1 hf
                exact ⟨a, ha⟩
              obtain ⟨a, ha⟩ := this
              obtain ⟨n0, hn0⟩ := ha.exists
              refine ⟨a, by rw [← hn0]; exact ha1 n0, ?_⟩
              refine tendsto_nhds_unique (hL θ w) ((hS θ a).congr' ?_)
              filter_upwards [ha] with n hn
              rw [ha2 n, hn]
            · intro α β a hab hlt
              have hev : ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ), x n α a < x n β a :=
                (hY α a).eventually_lt (hY β a) hlt
              have : ∀ n, ∃ θ, (α ≤ θ ∧ θ ≤ β) ∧ (x n α a < x n β a → l n θ (N.G.head a) = T n θ a) := by
                intro n
                by_cases hc : x n α a < x n β a
                · obtain ⟨θ, hθ, he⟩ := e10 n α β a hab hc
                  exact ⟨θ, hθ, fun _ => he⟩
                · exact ⟨α, ⟨le_rfl, hab⟩, fun h => absurd h hc⟩
              choose θn g1 g2 using this
              obtain ⟨θ, h1, h2, h3⟩ := cpt α β θn g1
              refine ⟨θ, ⟨h1, h2⟩, ?_⟩
              have r : Filter.Tendsto (fun n => T n (θn n) a) (Filter.hyperfilter ℕ : Filter ℕ) (nhds (S θ a)) := by
                exact ((mL θn θ (N.G.head a) h3).max ((mL θn θ (N.G.tail a) h3).add_const (N.τ a))).congr (fun n => (e13 n (θn n) a).symm)
              apply tendsto_nhds_unique (mL θn θ (N.G.head a) h3)
              apply r.congr'
              filter_upwards [hev] with n hn
              exact (g2 n hn).symm
            · intro α β a hab
              exact le_of_tendsto_of_tendsto' ((hS α a).add (((hY β a).sub (hY α a)).div_const (N.ν a)))
                (hS β a) (fun n => e11 n α β a hab)
            · intro α β a hα hab
              exact le_of_tendsto_of_tendsto' (hS β a)
                ((((hL β (N.G.tail a)).add_const (N.τ a)).max (hS α a)).add
                  (((hY β a).sub (hY α a)).div_const (N.ν a))) (fun n => e12 n α β a hα hab)
          have ac_lemma : ∀ (F g : ℝ → ℝ) (_ : LocallyIntegrable g (volume : Measure ℝ))
              (_ : ∀ a b : ℝ, a ≤ b → |F b - F a| ≤ ∫ θ in a..b, g θ),
              (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧ LocallyIntegrable (deriv F : ℝ → ℝ) volume ∧
              (∀ᵐ u : ℝ, HasDerivAt F (deriv F u) u) ∧
              (∀ a b : ℝ, ∫ θ in a..b, deriv F θ = F b - F a) := by
            clear * -
            intro F g hg hF
            have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
              intervalIntegrable_iff.mpr <|
                (hg.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc
            have hAC : ∀ a b, AbsolutelyContinuousOnInterval F a b := by
              intro a b
              have h1 := (hgi a b).absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
              unfold AbsolutelyContinuousOnInterval at h1 ⊢
              refine squeeze_zero' ?_ ?_ h1
              · exact Filter.Eventually.of_forall fun E => Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)
              · refine Filter.Eventually.of_forall fun E => Finset.sum_le_sum fun i _ => ?_
                have key : ∀ p q : ℝ, p ≤ q →
                    dist (F p) (F q) ≤ dist (∫ v in a..p, g v) (∫ v in a..q, g v) := by
                  intro p q hpq
                  have h2 : (∫ v in a..q, g v) - (∫ v in a..p, g v) = ∫ v in p..q, g v :=
                    intervalIntegral.integral_interval_sub_left (hgi a q) (hgi a p)
                  rw [dist_comm, dist_comm (∫ v in a..p, g v), Real.dist_eq, Real.dist_eq, h2]
                  exact (hF p q hpq).trans (le_abs_self _)
                rcases le_total (E.2 i).1 (E.2 i).2 with h | h
                · exact key _ _ h
                · rw [dist_comm, dist_comm (∫ v in a..(E.2 i).1, g v)]
                  exact key _ _ h
            refine ⟨hAC, ?_, ?_, ?_⟩
            · intro x
              refine ⟨Set.Ioc (x - 1) (x + 1), Ioc_mem_nhds (by linarith) (by linarith), ?_⟩
              exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
                (hAC (x - 1) (x + 1)).intervalIntegrable_deriv
            · have h3 : ∀ n : ℕ, ∀ᵐ x : ℝ, x ∈ Set.uIcc (-(n:ℝ)) n → DifferentiableAt ℝ F x :=
                fun n => (hAC _ _).ae_differentiableAt
              filter_upwards [ae_all_iff.mpr h3] with x hx
              obtain ⟨n, hn⟩ := exists_nat_ge |x|
              have := abs_le.mp hn
              exact (hx n (by rw [Set.uIcc_of_le (by linarith)]; exact ⟨this.1, this.2⟩)).hasDerivAt
            · intro a b
              have h := AbsolutelyContinuousOnInterval.integral_deriv_eq_sub (f := F) (a := a) (b := b) (hAC a b)
              exact h
          have cont_of_AC : ∀ (f : ℝ → ℝ), (∀ a b, AbsolutelyContinuousOnInterval f a b) → Continuous f := by
            clear * -
            intro f hf
            apply continuous_iff_continuousAt.mpr
            intro u
            exact (hf (u-1) (u+1)).continuousOn.continuousAt (by
              rw [Set.uIcc_of_le (by linarith)]
              exact Icc_mem_nhds (by linarith) (by linarith))
          have E_inflow : ∀ (ν0 : ℝ → ℝ) (_ : IsInflowRate ν0),
              Monotone (cum ν0) ∧ Continuous (cum ν0) ∧ (∀ θ ≤ 0, cum ν0 θ = 0) ∧
              (∀ a b, ∫ θ in a..b, ν0 θ = cum ν0 b - cum ν0 a) ∧
              (∀ᵐ u, HasDerivAt (cum ν0) (ν0 u) u) := by
            clear * -
            intro ν0 h
            obtain ⟨h1, h2, h3⟩ := h
            have hii : ∀ a b, IntervalIntegrable ν0 volume a b := fun a b => ((LocallyIntegrable.integrableOn_isCompact h1 isCompact_uIcc).intervalIntegrable)
            have hsub : ∀ a b, ∫ θ in a..b, ν0 θ = cum ν0 b - cum ν0 a := by
              intro a b
              unfold cum
              rw [intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)]
            refine ⟨?_, intervalIntegral.continuous_primitive hii 0, ?_, hsub, ?_⟩
            · intro a b hab
              have : 0 ≤ ∫ θ in a..b, ν0 θ := intervalIntegral.integral_nonneg_of_ae hab h2
              rw [hsub] at this; linarith
            · intro θ hθ
              unfold cum
              rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hθ]
              rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
              rw [MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero]
              · simp
              · filter_upwards [h3] with a ha h' using ha h'.2
            · have := LocallyIntegrable.ae_hasDerivAt_integral h1
              filter_upwards [this] with u hu
              exact hu 0
          let g : ℝ → ℝ := Set.indicator (Set.Ici 0) (fun θ => ν0 (θ + ϑ))
          have hgLoc : LocallyIntegrable (fun θ => ν0 (θ + ϑ)) := by
            intro θ
            refine ⟨Set.Ioc (θ-1) (θ+1), Ioc_mem_nhds (by linarith) (by linarith), ?_⟩
            apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
            exact (IntervalIntegrable.comp_add_right_iff (f := ν0) (a := θ-1) (b := θ+1) (c := ϑ) (by finiteness)).mpr
              ((hν0.1.integrableOn_isCompact isCompact_uIcc).intervalIntegrable)
          have hg : IsInflowRate g := by
            refine ⟨hgLoc.indicator measurableSet_Ici, ?_, ?_⟩
            · have ha : ∀ᵐ θ : ℝ, 0 ≤ ν0 (θ + ϑ) := by
                exact (measurePreserving_add_right volume ϑ).quasiMeasurePreserving.ae hν0.2.1
              filter_upwards [ha] with θ hθ
              dsimp [g]
              by_cases h : θ ∈ Set.Ici (0:ℝ) <;> simp [h, hθ]
            · exact Filter.Eventually.of_forall fun θ hθ => by simp [g, not_le.mpr hθ]
          obtain ⟨hXm, hXc, hX0, hXi, hXd⟩ := E_inflow g hg
          let X := cum g
          have hpred : ∀ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧
              ℓ ϑ (N.G.tail a) + N.τ a ≤ ℓ ϑ w := by
            intro w hw
            have hr := hSPG.2 w
            cases hr with
            | refl => exact (hw rfl).elim
            | @tail u _ hr hab =>
              obtain ⟨a, ha1, ha2⟩ := hab
              refine ⟨a.1, ha2, ?_⟩
              have hm := a.2
              simp only [primeArcs, Finset.mem_filter, Finset.mem_univ, true_and] at hm
              have ha2' : N.G.head a.1 = w := ha2
              simpa only [ha2'] using hm
          obtain ⟨C, l, x, T, hC, hl0, hs, hx0, hlmod, hxmod, hnet, hleT, hpredT,
            hactive, hTlow, hTup, hTmax⟩ := limit_exists N hNstanding X hXm hXc hX0 (ℓ ϑ) hpred
          clear A_sum A_bdd A_max step_exists B_flowsum cut_bound B_growth B_flow_add disc
            C_ulim C_move C_tel C_approx limit_exists E_inflow hpred hSPG
          have hlmono : ∀ v, Monotone (fun θ => l θ v) := fun v α β hab => by
            linarith [(hlmod α β v hab).1]
          have hxmono : ∀ a, Monotone (fun θ => x θ a) := fun a α β hab => by
            linarith [(hxmod α β a hab).1]
          let G : ℝ → ℝ := fun θ => C * (1 + g θ)
          have hGL : LocallyIntegrable G := (locallyIntegrable_const 1 |>.add hg.1).continuous_mul continuous_const
          have hGi : ∀ a b, ∫ θ in a..b, G θ = C * (b - a + X b - X a) := by
            intro a b
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (by simp)
              ((hg.1.integrableOn_isCompact isCompact_uIcc).intervalIntegrable), hXi]
            simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, X]
            ring
          have hlAC : ∀ v, (∀ a b, AbsolutelyContinuousOnInterval (fun θ => l θ v) a b) ∧
              LocallyIntegrable (deriv (fun θ => l θ v)) ∧
              (∀ᵐ θ, HasDerivAt (fun u => l u v) (deriv (fun u => l u v) θ) θ) ∧
              (∀ a b, ∫ θ in a..b, deriv (fun u => l u v) θ = l b v - l a v) := by
            intro v
            apply ac_lemma _ G hGL
            intro a b hab
            rw [abs_of_nonneg (hlmod a b v hab).1, hGi]
            exact (hlmod a b v hab).2
          have hxAC := fun a => ac_lemma (fun θ => x θ a) g hg.1 (fun α β hab => by
            rw [abs_of_nonneg (hxmod α β a hab).1, hXi]
            exact (hxmod α β a hab).2)
          have hTmod : ∀ α β a, α ≤ β → 0 ≤ T β a - T α a ∧
              T β a - T α a ≤ C * (β - α + X β - X α) := by
            intro α β a hab
            have h1 := hlmod α β (N.G.head a) hab
            have h2 := hlmod α β (N.G.tail a) hab
            rw [hTmax, hTmax]
            constructor
            · have := max_le_max (by linarith [h1.1] : l α (N.G.head a) ≤ l β (N.G.head a))
                (by linarith [h2.1] : l α (N.G.tail a) + N.τ a ≤ l β (N.G.tail a) + N.τ a)
              linarith
            · have hh : l β (N.G.head a) ≤ l α (N.G.head a) + C * (β - α + X β - X α) := by linarith [h1.2]
              have ht : l β (N.G.tail a) + N.τ a ≤ (l α (N.G.tail a) + N.τ a) + C * (β - α + X β - X α) := by linarith [h2.2]
              have hm := max_le_max hh ht
              rw [max_add_add_right] at hm
              linarith
          have hTAC := fun a => ac_lemma (fun θ => T θ a) G hGL (fun α β hab => by
            rw [abs_of_nonneg (hTmod α β a hab).1, hGi]
            exact (hTmod α β a hab).2)
          have hWmono : ∀ a, Monotone (fun u => T u a - x u a / N.ν a) := by
            intro a α β hab
            have hm := hTlow α β a hab
            rw [sub_div] at hm
            linarith
          have hWflat : ∀ θ a, 0 < θ → l θ (N.G.tail a) + N.τ a < T θ a →
              (fun u => T u a - x u a / N.ν a) =ᶠ[nhds θ]
                (fun _ => T θ a - x θ a / N.ν a) := by
            intro θ a hθ hgap
            let c := (l θ (N.G.tail a) + N.τ a + T θ a) / 2
            have hc1 : l θ (N.G.tail a) + N.τ a < c := by dsimp [c]; linarith
            have hc2 : c < T θ a := by dsimp [c]; linarith
            have hlc : Continuous (fun u => l u (N.G.tail a) + N.τ a) :=
              (cont_of_AC _ (hlAC _).1).add_const _
            have hTc : Continuous (fun u => T u a) := cont_of_AC _ (hTAC a).1
            filter_upwards [Ioi_mem_nhds hθ, hlc.continuousAt.eventually (gt_mem_nhds hc1),
              hTc.continuousAt.eventually (lt_mem_nhds hc2)] with u hu hu1 hu2
            rcases le_total θ u with h | h
            · have h1 := hTlow θ u a h
              have h2 := hTup θ u a hθ.le h
              rw [max_eq_right (by linarith : l u (N.G.tail a) + N.τ a ≤ T θ a), sub_div] at h2
              rw [sub_div] at h1
              linarith
            · have h1 := hTlow u θ a h
              have h2 := hTup u θ a hu.le h
              rw [max_eq_right (by linarith : l θ (N.G.tail a) + N.τ a ≤ T u a), sub_div] at h2
              rw [sub_div] at h1
              linarith
          have hde : ∀ᵐ θ : ℝ, 0 < θ → DEDeriv N g l θ := by
            have hdL : ∀ᵐ θ, ∀ v, HasDerivAt (fun u => l u v) (deriv (fun u => l u v) θ) θ :=
              ae_all_iff.mpr fun v => (hlAC v).2.2.1
            have hdY : ∀ᵐ θ, ∀ a, HasDerivAt (fun u => x u a) (deriv (fun u => x u a) θ) θ :=
              ae_all_iff.mpr fun a => (hxAC a).2.2.1
            have hdT : ∀ᵐ θ, ∀ a, HasDerivAt (fun u => T u a) (deriv (fun u => T u a) θ) θ :=
              ae_all_iff.mpr fun a => (hTAC a).2.2.1
            filter_upwards [hdL, hdY, hdT, hXd] with θ hdL hdY hdT hdX hθ
            let d : N.G.V → ℝ := fun v => deriv (fun u => l u v) θ
            let y : N.G.A → ℝ := fun a => deriv (fun u => x u a) θ
            let q : N.G.A → ℝ := fun a => deriv (fun u => T u a) θ
            have hdz : ∀ a, 0 ≤ y a := fun a => (hdY a).nonneg_of_monotone (hxmono a)
            have hdn : ∀ v, 0 ≤ d v := fun v => (hdL v).nonneg_of_monotone (hlmono v)
            have hqd : ∀ a, l θ (N.G.head a) = T θ a → d (N.G.head a) = q a := by
              intro a ha
              have hm : IsLocalMin (fun u => T u a - l u (N.G.head a)) θ := by
                refine Filter.Eventually.of_forall fun u => ?_
                dsimp only
                rw [ha, sub_self]
                linarith [hleT u a]
              have he := hm.hasDerivAt_eq_zero ((hdT a).sub (hdL (N.G.head a)))
              dsimp [d, q]; linarith
            have hqt : ∀ a, l θ (N.G.tail a) + N.τ a = T θ a → d (N.G.tail a) = q a := by
              intro a ha
              have hm : IsLocalMin (fun u => T u a - (l u (N.G.tail a) + N.τ a)) θ := by
                refine Filter.Eventually.of_forall fun u => ?_
                dsimp only
                rw [ha, sub_self]
                have hh : l u (N.G.tail a) + N.τ a ≤ T u a := by
                  rw [hTmax]; exact le_max_right _ _
                linarith
              have he := hm.hasDerivAt_eq_zero ((hdT a).sub ((hdL (N.G.tail a)).add_const _))
              dsimp [d, q]; linarith
            have hqge : ∀ a, y a / N.ν a ≤ q a := by
              intro a
              have hh := ((hdT a).sub ((hdY a).div_const (N.ν a))).nonneg_of_monotone (hWmono a)
              dsimp [q, y]; linarith
            have hqeq : ∀ a, l θ (N.G.tail a) + N.τ a < T θ a → q a = y a / N.ν a := by
              intro a ha
              have hd := (hdT a).sub ((hdY a).div_const (N.ν a))
              have hz := (hasDerivAt_const θ (T θ a - x θ a / N.ν a)).congr_of_eventuallyEq (hWflat θ a hθ ha)
              have he := hd.unique hz
              dsimp [q, y]; linarith
            have hy0 : ∀ a, ¬ a ∈ primeArcs N (l θ) → y a = 0 := by
              intro a ha
              have hg : l θ (N.G.head a) < l θ (N.G.tail a) + N.τ a := by
                simpa only [primeArcs, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using ha
              have hc1 : Continuous (fun u => l u (N.G.head a)) := cont_of_AC _ (hlAC _).1
              have hc2 : Continuous (fun u => l u (N.G.tail a) + N.τ a) :=
                (cont_of_AC _ (hlAC _).1).add_const _
              have hev : ∀ᶠ u in nhds θ, l u (N.G.head a) < T u a := by
                filter_upwards [hc1.continuousAt.eventually_lt hc2.continuousAt hg] with u hu
                rw [hTmax]
                exact hu.trans_le (le_max_right _ _)
              obtain ⟨δ, hδ, hδprop⟩ := Metric.eventually_nhds_iff.mp hev
              have heq : (fun u => x u a) =ᶠ[nhds θ] (fun _ => x θ a) := by
                filter_upwards [Metric.ball_mem_nhds θ hδ] with u hu
                have huneq : dist u θ < δ := hu
                have hconst : ∀ α β, α ≤ β → θ-δ < α → β < θ+δ → x α a = x β a := by
                  intro α β hab hα hβ
                  apply le_antisymm (hxmono a hab)
                  by_contra hc
                  have hpos : x α a < x β a := lt_of_not_ge hc
                  obtain ⟨v, hv, he⟩ := hactive α β a hab hpos
                  have hh := hδprop (y := v) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hv.1, hv.2])
                  exact hh.ne he
                rw [Real.dist_eq, abs_lt] at huneq
                rcases le_total u θ with h | h
                · exact hconst u θ h (by linarith [huneq.1]) (by linarith)
                · exact (hconst θ u h (by linarith) (by linarith [huneq.2])).symm
              exact (hdY a).unique ((hasDerivAt_const θ (x θ a)).congr_of_eventuallyEq heq)
            have hlabels : ∀ a : (Gprime N (l θ)).A,
                d (N.G.head a.1) = rhoArc (starArcs N (l θ)) (nuPrime N (l θ)) a
                  (d (N.G.tail a.1)) (y a.1) := by
              intro a
              have ha := a.2
              simp only [primeArcs, Finset.mem_filter, Finset.mem_univ, true_and] at ha
              have he : l θ (N.G.head a.1) = T θ a.1 := by
                rw [hTmax, max_eq_left ha]
              have hd := hqd a.1 he
              unfold rhoArc
              by_cases hstar : a ∈ starArcs N (l θ)
              · rw [if_pos hstar]
                have hgap : l θ (N.G.tail a.1) + N.τ a.1 < l θ (N.G.head a.1) := by
                  simpa only [starArcs, Finset.mem_filter, Finset.mem_univ, true_and] using hstar
                have hh := hqeq a.1 (by rwa [← he])
                exact hd.trans hh
              · rw [if_neg hstar]
                have heq : l θ (N.G.tail a.1) + N.τ a.1 = T θ a.1 := by
                  have hn : ¬ l θ (N.G.tail a.1) + N.τ a.1 < l θ (N.G.head a.1) := by
                    simpa only [starArcs, Finset.mem_filter, Finset.mem_univ, true_and] using hstar
                  linarith
                have ht := hqt a.1 heq
                dsimp [nuPrime]
                rw [hd, ht, max_eq_left (hqge a.1)]
            have hsum : ∀ (f : N.G.A → N.G.V) v,
                (∑ a : (Gprime N (l θ)).A, if f a.1 = v then y a.1 else 0) =
                  ∑ a : N.G.A, if f a = v then y a else 0 := by
              intro f v
              change (∑ a : {a : N.G.A // a ∈ primeArcs N (l θ)}, if f a.1 = v then y a.1 else 0) =
                ∑ a : N.G.A, if f a = v then y a else 0
              rw [← Finset.sum_subtype (primeArcs N (l θ)) (fun _ => Iff.rfl) (fun a => if f a = v then y a else 0)]
              apply Finset.sum_subset (Finset.subset_univ _)
              intro a _ ha
              simp [hy0 a ha]
            have hstatic : IsStaticFlow (Gprime N (l θ)) (fun a => y a.1) (g θ) := by
              have hn : ∀ v, outflow N.G y v - inflow N.G y v =
                  (if v = N.G.s then g θ else 0) - (if v = N.G.t then g θ else 0) := by
                intro v
                have hd1 : HasDerivAt (fun u => outflow N.G (x u) v - inflow N.G (x u) v)
                    (outflow N.G y v - inflow N.G y v) θ := by
                  unfold outflow inflow
                  exact (HasDerivAt.fun_sum fun a _ => hdY a).sub (HasDerivAt.fun_sum fun a _ => hdY a)
                have hd2 : HasDerivAt (fun u => outflow N.G (x u) v - inflow N.G (x u) v)
                    ((if v = N.G.s then g θ else 0) - (if v = N.G.t then g θ else 0)) θ := by
                  simp_rw [hnet]
                  apply HasDerivAt.sub
                  · split_ifs
                    · exact hdX
                    · exact hasDerivAt_const _ _
                  · split_ifs
                    · exact hdX
                    · exact hasDerivAt_const _ _
                exact hd1.unique hd2
              have hO : ∀ v, outflow (Gprime N (l θ)) (fun a => y a.1) v = outflow N.G y v := by
                intro v
                simp only [outflow, Finset.sum_filter]
                exact hsum N.G.tail v
              have hI : ∀ v, inflow (Gprime N (l θ)) (fun a => y a.1) v = inflow N.G y v := by
                intro v
                simp only [inflow, Finset.sum_filter]
                exact hsum N.G.head v
              refine ⟨fun a => hdz a.1, ?_, ?_⟩
              · intro v hvs hvt
                change N.G.V at v
                have hv1 : v ≠ N.G.s := hvs
                have hv2 : v ≠ N.G.t := hvt
                exact (congrArg₂ (fun a b : ℝ => a - b) (hO v) (hI v)).trans
                  ((hn v).trans (by rw [if_neg hv1, if_neg hv2, sub_self]))
              · rw [hO, hI]
                change outflow N.G y N.G.s - inflow N.G y N.G.s = g θ
                exact (hn N.G.s).trans (by rw [if_pos rfl, if_neg hst, sub_zero])
            refine ⟨d, hasDerivAt_pi.mpr hdL, ?_, fun hnot => ?_⟩
            · intro hsp
              refine ⟨?_, fun a => y a.1, hstatic, hdn, ?_, fun a _ => hlabels a⟩
              · have hdsrc : HasDerivAt (fun u => l u N.G.s) 1 θ := by
                  simp_rw [hs]
                  exact (hasDerivAt_id θ).add_const _
                exact (hdL N.G.s).unique hdsrc
              · intro w hw
                obtain ⟨a, ha, he⟩ := hpredT θ w hw
                have hm : a ∈ primeArcs N (l θ) := by
                  simp only [primeArcs, Finset.mem_filter, Finset.mem_univ, true_and]
                  rw [ha, he, hTmax]
                  exact le_max_right _ _
                refine ⟨⟨⟨a, hm⟩, ha, ?_⟩, ?_⟩
                · rw [← ha]; exact hlabels ⟨a, hm⟩
                · rintro r ⟨a, ha, rfl⟩
                  rw [← ha]
                  exact (hlabels a).le
            · exfalso
              apply hnot
              refine ⟨hAcyc (l θ), ?_⟩
              intro v
              induction v using (wf0 N hNstanding (l θ)).induction with
              | _ v ih =>
                by_cases hv : v = N.G.s
                · subst hv; exact Relation.ReflTransGen.refl
                · obtain ⟨a, ha, he⟩ := hpredT θ v hv
                  have hineq : l θ (N.G.tail a) + N.τ a ≤ l θ v := by
                    rw [he, hTmax]; exact le_max_right _ _
                  have hpred := ih (N.G.tail a) ⟨a, rfl, ha, hineq⟩
                  exact Relation.ReflTransGen.tail hpred
                    ⟨⟨a, by simp only [primeArcs, Finset.mem_filter, Finset.mem_univ, true_and]; rwa [ha]⟩, rfl, ha⟩
          let k : ℝ → N.G.V → ℝ := fun θ => l (θ - ϑ)
          let H : ℝ → ℝ := fun θ => G (θ - ϑ)
          have hHL : LocallyIntegrable H := by
            intro θ
            refine ⟨Set.Ioc (θ-1) (θ+1), Ioc_mem_nhds (by linarith) (by linarith), ?_⟩
            apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
            change IntervalIntegrable (fun u => G (u + (-ϑ))) volume (θ-1) (θ+1)
            exact (IntervalIntegrable.comp_add_right_iff (f := G) (a := θ-1) (b := θ+1) (c := -ϑ) (by finiteness)).mpr
              ((hGL.integrableOn_isCompact isCompact_uIcc).intervalIntegrable)
          have hkAC : ∀ v a b, AbsolutelyContinuousOnInterval (fun θ => k θ v) a b := by
            intro v
            apply (ac_lemma (fun θ => k θ v) H hHL ?_).1
            intro a b hab
            have hh := hlmod (a - ϑ) (b - ϑ) v (by linarith)
            rw [abs_of_nonneg hh.1]
            change l (b - ϑ) v - l (a - ϑ) v ≤ ∫ θ in a..b, G (θ - ϑ)
            rw [intervalIntegral.integral_comp_sub_right, hGi]
            convert hh.2 using 1 <;> ring
          have hkde : ∀ᵐ θ : ℝ, ϑ < θ → DEDeriv N ν0 k θ := by
            have ht : ∀ᵐ θ : ℝ, 0 < θ - ϑ → DEDeriv N g l (θ - ϑ) := by
              simpa only [sub_eq_add_neg] using
                (measurePreserving_add_right volume (-ϑ)).quasiMeasurePreserving.ae hde
            filter_upwards [ht] with θ ht hθ
            obtain ⟨d, hd, hr⟩ := ht (by linarith)
            refine ⟨d, hd.comp_sub_const θ ϑ, ?_⟩
            have he : g (θ - ϑ) = ν0 θ := by
              simp [g, show (0:ℝ) ≤ θ - ϑ by linarith]
            simpa only [he] using hr
          let ℓ' : ℝ → N.G.V → ℝ := fun θ => ℓ (min θ ϑ) + k θ - k (min θ ϑ)
          have hle : ∀ θ ≤ ϑ, ℓ' θ = ℓ θ := by
            intro θ hθ
            dsimp [ℓ']
            rw [min_eq_left hθ]
            abel
          have hge : ∀ θ, ϑ ≤ θ → ℓ' θ = k θ := by
            intro θ hθ
            have hk0 : k ϑ = ℓ ϑ := by simpa [k] using hl0
            dsimp [ℓ']
            rw [min_eq_right hθ, hk0]
            abel
          refine ⟨1, one_pos, ℓ', hle, ?_, ?_, ?_⟩
          · intro v a b _ _
            have h1 := hACmin (fun θ => ℓ θ v) ϑ a b
              (hℓ.1 v _ _ (min_le_right _ _) (min_le_right _ _))
            have h2 := hkAC v a b
            have h3 := hACmin (fun θ => k θ v) ϑ a b (hkAC v _ _)
            exact (h1.add h2).sub h3
          · intro θ hθ v
            rw [hle θ (by linarith)]
            exact hℓ.2.1 θ hθ v
          · have hne : ∀ᵐ θ : ℝ, θ ∉ ({ϑ} : Set ℝ) :=
              measure_eq_zero_iff_ae_notMem.mp Real.volume_singleton
            filter_upwards [hℓ.2.2, hkde, hne] with θ hold hnew hne hθ _
            have hn : θ ≠ ϑ := hne
            rcases lt_or_gt_of_ne hn with hlt | hgt
            · obtain ⟨d, hd, hr⟩ := hold hθ hlt
              have heq : ℓ' =ᶠ[nhds θ] ℓ := by
                filter_upwards [Iio_mem_nhds hlt] with u hu using hle u hu.le
              refine ⟨d, hd.congr_of_eventuallyEq heq, ?_⟩
              rw [hle θ hlt.le]
              exact hr
            · obtain ⟨d, hd, hr⟩ := hnew hgt
              have heq : ℓ' =ᶠ[nhds θ] k := by
                filter_upwards [Ioi_mem_nhds hgt] with u hu using hge u hu.le
              refine ⟨d, hd.congr_of_eventuallyEq heq, ?_⟩
              rw [hge θ hgt.le]
              exact hr
        ·
          set L := ℓ ϑ with hLdef
          set e : N.G.V → ℝ := fun v => if Reaches (Gprime N L) N.G.s v then 0 else 1 with he
          obtain ⟨α, hα, hgap⟩ : ∃ α > 0, ∀ a, L (N.G.head a) < L (N.G.tail a) + N.τ a →
              α < L (N.G.tail a) + N.τ a - L (N.G.head a) := by
            let g : N.G.A → ℝ := fun a => if L (N.G.head a) < L (N.G.tail a) + N.τ a then
              L (N.G.tail a) + N.τ a - L (N.G.head a) else 1
            have hg : ∀ a, 0 < g a := by
              intro a; simp only [g]; split_ifs with h <;> linarith
            let S : Finset ℝ := Finset.univ.image g ∪ {1}
            have hS : S.Nonempty := ⟨1, by simp [S]⟩
            have hpos : 0 < S.min' hS := by
              have hm := Finset.min'_mem S hS
              simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hm
              rcases hm with ⟨a, _, ha⟩ | hm
              · rw [← ha]; exact hg a
              · rw [hm]; norm_num
            refine ⟨S.min' hS / 2, by linarith, fun a ha => ?_⟩
            have : S.min' hS ≤ g a := Finset.min'_le _ _ (by simp [S])
            simp only [g, if_pos ha] at this
            linarith
          have hreach : ∀ h : ℝ, 0 ≤ h → h < α → ∀ v,
              Reaches (Gprime N (fun w => L w + h * e w)) N.G.s v ↔
                Reaches (Gprime N L) N.G.s v := by
            intro h h0 hα' v
            constructor
            · intro hr
              unfold Reaches at hr ⊢
              induction hr with
              | refl => exact Relation.ReflTransGen.refl
              | @tail u w _ hab ih =>
                obtain ⟨b, hb1, hb2⟩ := hab
                have hb := b.2
                simp only [primeArcs, Finset.mem_filter, Finset.mem_univ, true_and] at hb
                have e1 : N.G.tail b.1 = u := hb1
                have e2 : N.G.head b.1 = w := hb2
                rw [e1, e2] at hb
                have heu : e u = 0 := by simp only [he]; exact if_pos ih
                rw [heu] at hb
                by_cases hin : L u + N.τ b.1 ≤ L w
                · exact Relation.ReflTransGen.tail ih
                    ⟨⟨b.1, by simp only [primeArcs, Finset.mem_filter, Finset.mem_univ, true_and]; rw [e1, e2]; exact hin⟩, e1, e2⟩
                · push Not at hin
                  have := hgap b.1 (by rw [e1, e2]; exact hin)
                  rw [e1, e2] at this
                  have hew : e w ≤ 1 := by simp only [he]; split_ifs <;> norm_num
                  have hew0 : 0 ≤ e w := by simp only [he]; split_ifs <;> norm_num
                  nlinarith
            · intro hr
              unfold Reaches at hr ⊢
              induction hr with
              | refl => exact Relation.ReflTransGen.refl
              | @tail u w hsu hab ih =>
                obtain ⟨b, hb1, hb2⟩ := hab
                have hb := b.2
                simp only [primeArcs, Finset.mem_filter, Finset.mem_univ, true_and] at hb
                have e1 : N.G.tail b.1 = u := hb1
                have e2 : N.G.head b.1 = w := hb2
                rw [e1, e2] at hb
                have hw : Reaches (Gprime N L) N.G.s w := Relation.ReflTransGen.tail hsu ⟨b, hb1, hb2⟩
                have heu : e u = 0 := by simp only [he]; exact if_pos hsu
                have hew : e w = 0 := by simp only [he]; exact if_pos hw
                exact Relation.ReflTransGen.tail ih
                  ⟨⟨b.1, by simp only [primeArcs, Finset.mem_filter, Finset.mem_univ, true_and]; rw [e1, e2, heu, hew]; linarith⟩, e1, e2⟩
          set ℓ' : ℝ → N.G.V → ℝ := fun θ v => ℓ (min θ ϑ) v + e v * max (θ - ϑ) 0 with hℓ'
          have hle : ∀ θ ≤ ϑ, ℓ' θ = ℓ θ := by
            intro θ hθ
            funext v
            simp only [hℓ', min_eq_left hθ, max_eq_right (by linarith : θ - ϑ ≤ 0), mul_zero, add_zero]
          have hgt : ∀ θ, ϑ ≤ θ → ℓ' θ = fun w => L w + (θ - ϑ) * e w := by
            intro θ hθ
            funext v
            simp only [hℓ', min_eq_right hθ, max_eq_left (by linarith : 0 ≤ θ - ϑ), hLdef]
            ring
          refine ⟨α, hα, ℓ', hle, ?_, ?_, ?_⟩
          · intro v a b _ _
            have h1 := hACmin (fun θ => ℓ θ v) ϑ a b (hℓ.1 v _ _ (min_le_right _ _) (min_le_right _ _))
            have hlip : LipschitzWith 1 (fun θ : ℝ => max (θ - ϑ) 0) :=
              LipschitzWith.of_dist_le_mul fun x y => by
                simp only [Real.dist_eq, NNReal.coe_one, one_mul]
                exact (abs_max_sub_max_le_abs _ _ _).trans (by ring_nf; exact le_refl _)
            have h2 := (hlip.lipschitzOnWith (s := Set.uIcc a b)).absolutelyContinuousOnInterval
            have h3 := h2.const_mul (e v)
            exact h1.add h3
          · intro θ hθ v
            rw [hle θ (by linarith)]
            exact hℓ.2.1 θ hθ v
          · have hne : ∀ᵐ θ : ℝ, θ ∉ ({ϑ} : Set ℝ) :=
              measure_eq_zero_iff_ae_notMem.mp Real.volume_singleton
            filter_upwards [hℓ.2.2, hne] with θ h1 h2 h0 hlt
            have h2' : θ ≠ ϑ := h2
            rcases lt_or_gt_of_ne h2' with hlt' | hgt'
            · obtain ⟨d, hd, hr⟩ := h1 h0 hlt'
              have heq : ℓ' =ᶠ[nhds θ] ℓ := by
                filter_upwards [Iio_mem_nhds hlt'] with x hx
                exact hle x (le_of_lt hx)
              refine ⟨d, hd.congr_of_eventuallyEq heq, ?_⟩
              rw [hle θ hlt'.le]
              exact hr
            · refine ⟨e, ?_, ?_⟩
              · have heq : ℓ' =ᶠ[nhds θ] fun x => L + (x - ϑ) • e := by
                  filter_upwards [Ioi_mem_nhds hgt'] with x hx
                  rw [hgt x (le_of_lt hx)]
                  funext w
                  simp [smul_eq_mul]
                have : HasDerivAt (fun x => L + (x - ϑ) • e) e θ := by
                  simpa using (((hasDerivAt_id θ).sub_const ϑ).smul_const e).const_add L
                exact this.congr_of_eventuallyEq heq
              · rw [hgt θ hgt'.le]
                have hR := hreach (θ - ϑ) (by linarith) (by linarith)
                refine ⟨fun hS => absurd ⟨hAcyc L, fun v => (hR v).1 (hS.2 v)⟩ hSPG,
                  fun _ v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
                · have : Reaches (Gprime N L) N.G.s v := (hR v).1 hv
                  simp only [he]; exact if_pos this
                · have : ¬ Reaches (Gprime N L) N.G.s v := fun h => hv ((hR v).2 h)
                  simp only [he]; exact if_neg this
