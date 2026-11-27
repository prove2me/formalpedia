-- Prove2me | solution 1 for ThinFlowSP.Breakpoints.Supplement.theorem_24
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:37.282907+00:00
-- url     : https://prove2.me/submissions/e1aa67b9-785f-45bc-a29a-2b0e14caddf7

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
    (hrm : RightMonotone ν0) :
    ∃ fp fm : N.G.A → ℝ → ℝ, IsDynEq N ν0 fp fm := by
      have A_sum : ∀ (G : Net) (W : Finset G.V) (y : G.A → ℝ),
          ∑ w ∈ W, (inflow G y w - outflow G y w) =
            ∑ a, y a * ((if G.head a ∈ W then 1 else 0) - (if G.tail a ∈ W then 1 else 0)) := by
        clear hrm hν0 ν0 hN N 
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
        clear hrm hν0 ν0 hN N 
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
        clear hrm hν0 ν0 hN N A_sum
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
        -- raising
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
        clear hrm hν0 ν0 hN N 
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
        -- limits
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
        clear hrm hν0 ν0 hN N step_exists A_max A_bdd A_sum

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
        clear hrm hν0 ν0 hN N wf0 step_exists A_max A_bdd A_sum
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
        clear hrm hν0 ν0 hN N step_exists A_max A_bdd A_sum
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
        clear hrm hν0 ν0 hN N cut_bound B_flowsum step_exists A_max A_bdd A_sum
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
      have B_init : ∀ (N : QNet) (_ : N.Standing), ∃ l0 : N.G.V → ℝ, l0 N.G.s = 0 ∧
          (∀ a, l0 (N.G.head a) ≤ l0 (N.G.tail a) + N.τ a) ∧
          (∀ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l0 (N.G.tail a) + N.τ a = l0 w) := by
        clear hrm hν0 ν0 hN N B_growth B_flowsum A_max A_bdd A_sum
        intro N hN
        obtain ⟨l, y, hs, hy, hnet, h1, h2, h3⟩ := step_exists N hN (fun _ => -1) 0 0 le_rfl
        have hy0 : ∀ a, y a = 0 := by
          intro a
          refine le_antisymm ?_ (hy a)
          exact cut_bound N hN l y 0 le_rfl hy hnet (fun a ha => (le_max_left _ _).trans (h2 a ha)) a
        have hl : ∀ v, 0 ≤ l v := by
          intro v
          have hwf := wf0 N hN l
          induction v using hwf.induction with
          | _ w ih =>
            by_cases hw : w = N.G.s
            · rw [hw, hs]
            · obtain ⟨a, rfl, h4⟩ := h3 w hw
              have h5 := (le_max_left _ _).trans h4
              have := ih (N.G.tail a) ⟨a, rfl, rfl, h5⟩
              linarith [hN.2.2.1 a]
        have hmax : ∀ a, max (l (N.G.tail a) + N.τ a) ((-1 : ℝ) + y a / N.ν a) = l (N.G.tail a) + N.τ a := by
          intro a
          rw [hy0 a, zero_div]
          apply max_eq_left
          linarith [hl (N.G.tail a), hN.2.2.1 a]
        have h1' : ∀ a, l (N.G.head a) ≤ l (N.G.tail a) + N.τ a := by
          intro a
          have := h1 a
          rwa [hmax] at this
        refine ⟨l, hs, h1', ?_⟩
        intro w hw
        obtain ⟨a, rfl, h4⟩ := h3 w hw
        rw [hmax] at h4
        exact ⟨a, rfl, le_antisymm h4 (h1' a)⟩
      have B_flow_add : ∀ (G : Net) (x y : G.A → ℝ) (v : G.V),
          outflow G (fun a => x a + y a) v - inflow G (fun a => x a + y a) v =
            (outflow G x v - inflow G x v) + (outflow G y v - inflow G y v) := by
        clear hrm hν0 ν0 hN N B_init B_growth cut_bound B_flowsum wf0 step_exists A_max A_bdd A_sum
        intro G x y v
        simp only [outflow, inflow, Finset.sum_add_distrib]
        ring
      have disc : ∀ (N : QNet) (_ : N.Standing) (X : ℝ → ℝ) (_ : Monotone X) (_ : X 0 = 0),
          ∃ (C : ℝ) (l0 : N.G.V → ℝ), 0 ≤ C ∧ ∀ h : ℝ, 0 < h →
            ∃ (l : ℕ → N.G.V → ℝ) (x T : ℕ → N.G.A → ℝ),
              l 0 = l0 ∧ (∀ a, x 0 a = 0) ∧ (∀ k : ℕ, l k N.G.s = k * h) ∧
              (∀ k a, l k (N.G.head a) ≤ T k a) ∧
              (∀ k w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l k w = T k a) ∧
              (∀ (k : ℕ) v, outflow N.G (x k) v - inflow N.G (x k) v =
                (if v = N.G.s then X (k * h) else 0) - (if v = N.G.t then X (k * h) else 0)) ∧
              (∀ (k : ℕ) v, 0 ≤ l (k+1) v - l k v ∧
                l (k+1) v - l k v ≤ C * (h + X ((k+1 : ℕ) * h) - X (k * h))) ∧
              (∀ (k : ℕ) a, 0 ≤ x (k+1) a - x k a ∧
                x (k+1) a - x k a ≤ X ((k+1 : ℕ) * h) - X (k * h)) ∧
              (∀ k a, x k a < x (k+1) a → l (k+1) (N.G.head a) = T (k+1) a) ∧
              (∀ a, T 0 a = l 0 (N.G.tail a) + N.τ a) ∧
              (∀ k a, T (k+1) a = max (l (k+1) (N.G.tail a) + N.τ a)
                (T k a + (x (k+1) a - x k a) / N.ν a)) := by 
        clear hrm hν0 ν0 hN N B_flowsum wf0 A_max A_bdd A_sum
        intro N hN X hX hX0
        obtain ⟨l0, hl0s, hl0a, hl0p⟩ := B_init N hN
        have hν := hN.2.1
        have hC : 0 ≤ ∑ a, 1 / N.ν a := Finset.sum_nonneg (fun a _ => (one_div_pos.2 (hν a)).le)
        refine ⟨1 + ∑ a, 1 / N.ν a, l0, by linarith, ?_⟩
        intro h hh
        have hM : ∀ k : ℕ, 0 ≤ X ((k + 1 : ℕ) * h) - X (k * h) := by
          intro k
          have : X (k * h) ≤ X ((k + 1 : ℕ) * h) := by
            apply hX
            apply mul_le_mul_of_nonneg_right _ hh.le
            exact_mod_cast Nat.le_succ k
          linarith
        have hstep := fun (k : ℕ) (T0 : N.G.A → ℝ) => step_exists N hN T0 ((k + 1 : ℕ) * h) _ (hM k)
        choose L Y hLs hY hnet hL1 hL2 hL3 using hstep
        obtain ⟨T, hT0, hTs⟩ : ∃ T : ℕ → N.G.A → ℝ, (T 0 = fun a => l0 (N.G.tail a) + N.τ a) ∧
            ∀ k, T (k + 1) = fun a => max (L k (T k) (N.G.tail a) + N.τ a) (T k a + Y k (T k) a / N.ν a) :=
          ⟨fun k => Nat.rec (fun a => l0 (N.G.tail a) + N.τ a) (fun k Tk => fun a => max (L k Tk (N.G.tail a) + N.τ a) (Tk a + Y k Tk a / N.ν a)) k, rfl, fun k => rfl⟩
        obtain ⟨l, hl0, hls⟩ : ∃ l : ℕ → N.G.V → ℝ, l 0 = l0 ∧ ∀ k, l (k + 1) = L k (T k) :=
          ⟨fun k => Nat.rec l0 (fun k _ => L k (T k)) k, rfl, fun k => rfl⟩
        obtain ⟨x, hx0, hxs⟩ : ∃ x : ℕ → N.G.A → ℝ, (∀ a, x 0 a = 0) ∧ ∀ k, x (k + 1) = fun a => x k a + Y k (T k) a :=
          ⟨fun k => Nat.rec (fun _ => 0) (fun k xk => fun a => xk a + Y k (T k) a) k, fun _ => rfl, fun k => rfl⟩
        have hle : ∀ k a, l k (N.G.head a) ≤ T k a := by
          intro k a
          cases k with
          | zero => rw [hl0, hT0]; exact hl0a a
          | succ k => rw [hls, hTs]; exact hL1 k (T k) a
        have hpred : ∀ k w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l k w = T k a := by
          intro k w hw
          cases k with
          | zero =>
            obtain ⟨a, rfl, h1⟩ := hl0p w hw
            refine ⟨a, rfl, ?_⟩
            rw [hl0, hT0]; exact h1.symm
          | succ k =>
            obtain ⟨a, rfl, h1⟩ := hL3 k (T k) w hw
            refine ⟨a, rfl, le_antisymm (hle _ _) ?_⟩
            rw [hls, hTs]; exact h1
        have hTge : ∀ k a, l k (N.G.tail a) + N.τ a ≤ T k a := by
          intro k a
          cases k with
          | zero => rw [hl0, hT0]
          | succ k => rw [hls, hTs]; exact le_max_left _ _
        have hYM : ∀ k a, Y k (T k) a ≤ X ((k + 1 : ℕ) * h) - X (k * h) := by
          intro k a
          exact cut_bound N hN (L k (T k)) (Y k (T k)) _ (hM k) (hY k (T k)) (hnet k (T k))
            (fun a ha => (le_max_left _ _).trans (hL2 k (T k) a ha)) a
        have hlsrc : ∀ k : ℕ, l k N.G.s = k * h := by
          intro k
          cases k with
          | zero => rw [hl0, hl0s]; simp
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
        clear hrm hν0 ν0 hN N disc B_flow_add B_init B_growth cut_bound B_flowsum wf0 step_exists A_max A_bdd A_sum
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
        clear hrm hν0 ν0 hN N C_ulim disc B_flow_add B_init B_growth cut_bound B_flowsum wf0 step_exists A_max A_bdd A_sum
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
          (_ : ∀ a, T 0 a = l 0 (N.G.tail a) + N.τ a)
          (_ : ∀ k a, T (k+1) a = max (l (k+1) (N.G.tail a) + N.τ a)
                (T k a + (x (k+1) a - x k a) / N.ν a)),
          (∀ (j k : ℕ) v, j ≤ k → 0 ≤ l k v - l j v ∧
            l k v - l j v ≤ C * (k * h - j * h + X (k * h) - X (j * h))) ∧
          (∀ (j k : ℕ) a, j ≤ k → 0 ≤ x k a - x j a ∧ x k a - x j a ≤ X (k * h) - X (j * h)) ∧
          (∀ (j k : ℕ) a, j ≤ k → x j a < x k a → ∃ i, j < i ∧ i ≤ k ∧ l i (N.G.head a) = T i a) ∧
          (∀ (j k : ℕ) a, j ≤ k → l j (N.G.tail a) + N.τ a + (x k a - x j a) / N.ν a ≤ T k a) ∧
          (∀ (k : ℕ) a, ∃ j, j ≤ k ∧ T k a = l j (N.G.tail a) + N.τ a + (x k a - x j a) / N.ν a) := by
        clear hrm hν0 ν0 hN N C_move C_ulim disc B_flow_add B_init B_growth cut_bound B_flowsum wf0 step_exists A_max A_bdd A_sum
        intro N hN X C h l x T h1 h2 h3 h4 h5
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro j k v hjk
          induction k, hjk using Nat.le_induction with
          | base => simp
          | succ k hk ih =>
            have := h1 k v
            push_cast at this ⊢
            constructor
            · linarith [this.1, ih.1]
            · nlinarith [this.2, ih.2]
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
          | base =>
            rcases j with _ | j
            · rw [h4]; simp
            · rw [h5]; simp
          | succ k hk ih =>
            rw [h5]
            refine le_trans ?_ (le_max_right _ _)
            have e : (x (k+1) a - x j a) / N.ν a = (x k a - x j a) / N.ν a
              + (x (k+1) a - x k a) / N.ν a := by ring
            rw [e]; linarith
        · intro k a
          induction k with
          | zero => exact ⟨0, le_refl _, by rw [h4]; simp⟩
          | succ k ih =>
            obtain ⟨j, hj, hT⟩ := ih
            rcases le_total (l (k+1) (N.G.tail a) + N.τ a)
                (T k a + (x (k+1) a - x k a) / N.ν a) with hc | hc
            · refine ⟨j, by omega, ?_⟩
              rw [h5, max_eq_right hc, hT]; ring
            · refine ⟨k+1, le_refl _, ?_⟩
              rw [h5, max_eq_left hc]; simp
      have C_approx : ∀ (N : QNet) (_ : N.Standing) (X : ℝ → ℝ) (_ : Monotone X)
          (_ : ∀ θ ≤ 0, X θ = 0),
          ∃ (C : ℝ) (l0 : N.G.V → ℝ), 0 ≤ C ∧ ∀ h : ℝ, 0 < h →
            ∃ (tn : ℝ → ℝ) (l : ℝ → N.G.V → ℝ) (x T : ℝ → N.G.A → ℝ),
            (∀ θ, θ - h ≤ tn θ ∧ tn θ ≤ θ) ∧
            (∀ v, l 0 v = l0 v) ∧
            (∀ θ, l θ N.G.s = tn θ) ∧ (∀ θ ≤ 0, ∀ a, x θ a = 0) ∧
            (∀ α β v, α ≤ β → 0 ≤ l β v - l α v ∧
              l β v - l α v ≤ C * (β - α + h + X β - X (α - h))) ∧
            (∀ α β a, α ≤ β → 0 ≤ x β a - x α a ∧ x β a - x α a ≤ X β - X (α - h)) ∧
            (∀ θ v, outflow N.G (x θ) v - inflow N.G (x θ) v =
              (if v = N.G.s then X (tn θ) else 0) - (if v = N.G.t then X (tn θ) else 0)) ∧
            (∀ θ a, l θ (N.G.head a) ≤ T θ a) ∧
            (∀ θ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l θ w = T θ a) ∧
            (∀ α β a, α ≤ β → x α a < x β a → ∃ θ ∈ Set.Icc α β, l θ (N.G.head a) = T θ a) ∧
            (∀ θ a, ∀ θ' ≤ θ, l θ' (N.G.tail a) + N.τ a + (x θ a - x θ' a) / N.ν a ≤ T θ a) ∧
            (∀ θ a, ∃ θ' ≤ θ, min θ 0 ≤ θ' ∧
              T θ a = l θ' (N.G.tail a) + N.τ a + (x θ a - x θ' a) / N.ν a) := by
        clear hrm hν0 ν0 hN N C_move C_ulim B_flow_add B_init B_growth cut_bound B_flowsum wf0 step_exists A_max A_bdd A_sum
        intro N hN X hX hX0
        obtain ⟨C, l0, hC, H⟩ := disc N hN X hX (hX0 0 le_rfl)
        refine ⟨C + 1, l0, by linarith, ?_⟩
        intro h hh
        obtain ⟨l, x, T, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := H h hh
        obtain ⟨f1, f2, f3, f4, f5⟩ := C_tel N hN X C h l x T e7 e8 e9 e10 e11
        -- index
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
          ?_, ?_⟩
        · intro v; simp [K00, e1]
        · intro θ; simp [e3]
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
        · intro θ a θ' hθ
          have g1 := f4 _ _ a (Kmono _ _ hθ)
          have m1 : min θ' 0 ≤ min θ 0 := min_le_min_right 0 hθ
          show l (K θ') (N.G.tail a) + min θ' 0 + N.τ a + (x (K θ) a - x (K θ') a) / N.ν a
            ≤ T (K θ) a + min θ 0
          linarith
        · intro θ a
          rcases le_total θ 0 with hc | hc
          · refine ⟨θ, le_rfl, min_le_left _ _, ?_⟩
            simp only [K0 θ hc, e10]
            ring
          · obtain ⟨j, hj, hT⟩ := f5 (K θ) a
            refine ⟨(j : ℝ) * h, ?_, ?_, ?_⟩
            · have := Kle θ hc
              have c : (j : ℝ) ≤ K θ := by exact_mod_cast hj
              have : (j : ℝ) * h ≤ K θ * h := by gcongr
              linarith
            · rw [min_eq_right hc]; positivity
            · have m : min ((j : ℝ) * h) 0 = 0 := min_eq_right (by positivity)
              simp only [Knat, m, min_eq_right hc, hT, add_zero]
      have limit_exists : ∀ (N : QNet) (_ : N.Standing) (X : ℝ → ℝ) (_ : Monotone X)
          (_ : Continuous X) (_ : ∀ θ ≤ 0, X θ = 0),
          ∃ (C : ℝ) (l : ℝ → N.G.V → ℝ) (x T : ℝ → N.G.A → ℝ), 0 ≤ C ∧
            (∀ θ, l θ N.G.s = θ) ∧ (∀ θ ≤ 0, ∀ a, x θ a = 0) ∧
            (∀ α β v, α ≤ β → 0 ≤ l β v - l α v ∧ l β v - l α v ≤ C * (β - α + X β - X α)) ∧
            (∀ α β a, α ≤ β → 0 ≤ x β a - x α a ∧ x β a - x α a ≤ X β - X α) ∧
            (∀ θ v, outflow N.G (x θ) v - inflow N.G (x θ) v =
              (if v = N.G.s then X θ else 0) - (if v = N.G.t then X θ else 0)) ∧
            (∀ θ a, l θ (N.G.head a) ≤ T θ a) ∧
            (∀ θ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l θ w = T θ a) ∧
            (∀ α β a, α ≤ β → x α a < x β a → ∃ θ ∈ Set.Icc α β, l θ (N.G.head a) = T θ a) ∧
            (∀ θ a, ∀ θ' ≤ θ, l θ' (N.G.tail a) + N.τ a + (x θ a - x θ' a) / N.ν a ≤ T θ a) ∧
            (∀ θ a, ∃ θ' ≤ θ, T θ a = l θ' (N.G.tail a) + N.τ a + (x θ a - x θ' a) / N.ν a) := by
        clear hrm hν0 ν0 hN N C_tel disc B_flow_add B_init B_growth cut_bound B_flowsum wf0 step_exists A_max A_bdd A_sum
        intro N hN X hX hXc hX0
        obtain ⟨C, l0, hC, H⟩ := C_approx N hN X hX hX0
        have hpos : ∀ n : ℕ, (0:ℝ) < 1 / ((n:ℝ) + 1) := fun n => by positivity
        choose tn l x T e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 using fun n : ℕ => H (1 / ((n:ℝ) + 1)) (hpos n)
        have hh : Filter.Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) (Filter.hyperfilter ℕ : Filter ℕ) (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat.mono_left Nat.hyperfilter_le_atTop
        have hle1 : ∀ n : ℕ, 1 / ((n:ℝ) + 1) ≤ 1 := fun n => by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
        have hX00 : ∀ θ, 0 ≤ X θ := by
          intro θ
          rcases le_total θ 0 with hc | hc
          · rw [hX0 θ hc]
          · rw [← hX0 0 le_rfl]; exact hX hc
        -- bounds
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
        have Tb : ∀ θ a, ∃ A B, ∀ n, A ≤ T n θ a ∧ T n θ a ≤ B := by
          intro θ a
          obtain ⟨B1, hB1⟩ := lb θ (N.G.head a)
          obtain ⟨B2, hB2⟩ := lb θ (N.G.tail a)
          refine ⟨-B1, B2 + N.τ a + X θ / N.ν a, fun n => ⟨(hB1 n).1.trans (e8 n θ a), ?_⟩⟩
          obtain ⟨θ', hθ', -, hT⟩ := e12 n θ a
          rw [hT]
          have h1 := (e5 n θ' θ (N.G.tail a) hθ').1
          have h2 := (hB2 n).2
          have h3 : (x n θ a - x n θ' a) / N.ν a ≤ X θ / N.ν a := by
            have := hN.2.1 a
            have := (xb n θ a).2
            have := (xb n θ' a).1
            gcongr
            linarith
          linarith
        have Ll : ∀ θ v, ∃ L, Filter.Tendsto (fun n => l n θ v) (Filter.hyperfilter ℕ : Filter ℕ) (nhds L) := by
          intro θ v
          obtain ⟨B, hB⟩ := lb θ v
          exact C_ulim _ _ _ hB
        have Lx : ∀ θ a, ∃ L, Filter.Tendsto (fun n => x n θ a) (Filter.hyperfilter ℕ : Filter ℕ) (nhds L) := by
          intro θ a
          exact C_ulim _ _ _ (fun n => xb n θ a)
        have LT : ∀ θ a, ∃ L, Filter.Tendsto (fun n => T n θ a) (Filter.hyperfilter ℕ : Filter ℕ) (nhds L) := by
          intro θ a
          obtain ⟨A, B, hB⟩ := Tb θ a
          exact C_ulim _ _ _ hB
        choose L hL using Ll
        choose Y hY using Lx
        choose S hS using LT
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
        -- T modulus at moving points
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
        have Tge : ∀ θ a, ∀ θ' ≤ θ, L θ' (N.G.tail a) + N.τ a + (Y θ a - Y θ' a) / N.ν a ≤ S θ a := by
          intro θ a θ' hθ
          exact le_of_tendsto_of_tendsto' (((hL θ' (N.G.tail a)).add_const (N.τ a)).add
            (((hY θ a).sub (hY θ' a)).div_const (N.ν a))) (hS θ a) (fun n => e11 n θ a θ' hθ)
        have cpt : ∀ (p q : ℝ) (θn : ℕ → ℝ), (∀ n, p ≤ θn n ∧ θn n ≤ q) → ∃ θ, p ≤ θ ∧ θ ≤ q ∧
            Filter.Tendsto θn (Filter.hyperfilter ℕ : Filter ℕ) (nhds θ) := by
          intro p q θn hθ
          obtain ⟨θ, hlim⟩ := C_ulim θn p q hθ
          exact ⟨θ, ge_of_tendsto' hlim (fun n => (hθ n).1), le_of_tendsto' hlim (fun n => (hθ n).2), hlim⟩
        have Teq : ∀ θ a, ∃ θ' ≤ θ, S θ a = L θ' (N.G.tail a) + N.τ a + (Y θ a - Y θ' a) / N.ν a := by
          intro θ a
          choose θn g1 g2 g3 using fun n => e12 n θ a
          obtain ⟨θ', h1, h2, h3⟩ := cpt (min θ 0) θ θn (fun n => ⟨g2 n, g1 n⟩)
          refine ⟨θ', h2, ?_⟩
          have r := ((mL θn θ' (N.G.tail a) h3).add_const (N.τ a)).add
            (((hY θ a).sub (mY θn θ' a h3)).div_const (N.ν a))
          exact tendsto_nhds_unique ((hS θ a)) (r.congr (fun n => (g3 n).symm))
        refine ⟨C, L, Y, S, hC, ?_, ?_, modL, modY, ?_, ?_, ?_, ?_, Tge, Teq⟩
        · intro θ
          exact tendsto_nhds_unique (hL θ N.G.s) ((tlim θ).congr (fun n => (e3 n θ).symm))
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
          apply le_antisymm
          · exact le_of_tendsto_of_tendsto' (hL θ _) (hS θ a) (fun n => e8 n θ a)
          · obtain ⟨θ', hθ', hT⟩ := Teq θ a
            rw [hT]
            -- approximate θ' by min θ' (θn n)
            have m : Filter.Tendsto (fun n => min θ' (θn n)) (Filter.hyperfilter ℕ : Filter ℕ) (nhds θ') := by
              have := (tendsto_const_nhds (x := θ') (f := (Filter.hyperfilter ℕ : Filter ℕ))).min h3
              rwa [min_eq_left hθ'] at this
            have r := ((mL _ θ' (N.G.tail a) m).add_const (N.τ a)).add
              (((mY θn θ a h3).sub (mY _ θ' a m)).div_const (N.ν a))
            refine le_of_tendsto_of_tendsto r (mL θn θ (N.G.head a) h3) ?_
            filter_upwards [hev] with n hn
            rw [g2 n hn]
            exact e11 n (θn n) a _ (min_le_right _ _)
      have ac_lemma : ∀ (F g : ℝ → ℝ) (_ : LocallyIntegrable g (volume : Measure ℝ))
          (_ : ∀ a b : ℝ, a ≤ b → |F b - F a| ≤ ∫ θ in a..b, g θ),
          (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧ LocallyIntegrable (deriv F : ℝ → ℝ) volume ∧
          (∀ᵐ u : ℝ, HasDerivAt F (deriv F u) u) ∧
          (∀ a b : ℝ, ∫ θ in a..b, deriv F θ = F b - F a) := by
        clear hrm hν0 ν0 hN N limit_exists C_approx C_tel C_move C_ulim disc B_flow_add B_init B_growth cut_bound B_flowsum wf0 step_exists A_max A_bdd A_sum
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
      have arc_lemma : ∀ (F g : ℝ → ℝ) (ν τ : ℝ) (_ : 0 < ν) (_ : 0 ≤ τ) (_ : LocallyIntegrable g (volume : Measure ℝ))
          (_ : ∀ a b : ℝ, a ≤ b → 0 ≤ F b - F a ∧ F b - F a ≤ ∫ θ in a..b, g θ) (_ : ∀ u : ℝ, u ≤ 0 → F u = 0),
          ∃ z Fm : ℝ → ℝ,
            (∀ u : ℝ, IsGreatest {r | ∃ u' ≤ u, r = F u - F u' - ν * (u - u')} (z u)) ∧
            (∀ u : ℝ, Fm (u + τ) = F u - z u) ∧ IsQueueSolution ν (deriv F) z ∧
            (∀ a b : ℝ, a ≤ b → 0 ≤ Fm b - Fm a ∧ Fm b - Fm a ≤ ν * (b - a)) ∧
            (∀ u : ℝ, u ≤ 0 → Fm u = 0) ∧
            (∀ u : ℝ, IsLeast {q | 0 ≤ q ∧ F u ≤ Fm (u + τ + q)} (z u / ν)) ∧
            (∀ u : ℝ, Fm (u + τ + z u / ν) = F u) := by
        clear hrm hν0 ν0 hN N limit_exists C_approx C_tel C_move C_ulim disc B_flow_add B_init B_growth cut_bound B_flowsum wf0 step_exists A_max A_bdd A_sum
        intro F g ν τ hν hτ hg hF hF0
        have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
          intervalIntegrable_iff.mpr <|
            (hg.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc
        obtain ⟨hFAC, -, hFd, -⟩ := ac_lemma F g hg (fun a b hab => by
          rw [abs_of_nonneg (hF a b hab).1]; exact (hF a b hab).2)
        have hFc : Continuous F := by
          rw [continuous_iff_continuousAt]
          intro x
          exact ((hFAC (x - 1) (x + 1)).continuousOn).continuousAt
            (by rw [Set.uIcc_of_le (by linarith)]; exact Icc_mem_nhds (by linarith) (by linarith))
        have hzex : ∀ u, ∃ z, IsGreatest {r | ∃ u' ≤ u, r = F u - F u' - ν * (u - u')} z := by
          intro u
          have hc : ContinuousOn (fun u' => F u - F u' - ν * (u - u')) (Set.Icc (min 0 u) u) := by
            fun_prop
          obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn
            (Set.nonempty_Icc.mpr (min_le_right 0 u)) hc
          refine ⟨F u - F m - ν * (u - m), ⟨m, hm.2, rfl⟩, ?_⟩
          rintro r ⟨u', hu', rfl⟩
          by_cases h : min 0 u ≤ u'
          · exact hmax ⟨h, hu'⟩
          · push Not at h
            have h1 : F (min 0 u) = 0 := hF0 _ (min_le_left _ _)
            have h2 : F u' = 0 := hF0 _ (h.le.trans (min_le_left _ _))
            have h3 := hmax (show min 0 u ∈ Set.Icc (min 0 u) u from ⟨le_rfl, min_le_right _ _⟩)
            simp only [Set.mem_ofPred_eq] at h3
            rw [h1] at h3
            rw [h2]
            refine le_trans ?_ h3
            nlinarith
        choose z hz using hzex
        have hz0 : ∀ u, 0 ≤ z u := fun u => (hz u).2 ⟨u, le_rfl, by ring⟩
        have hlow : ∀ r u, r ≤ u → z r + (F u - F r) - ν * (u - r) ≤ z u := by
          intro r u hru
          obtain ⟨u', hu', he⟩ := (hz r).1
          have := (hz u).2 ⟨u', hu'.trans hru, rfl⟩
          rw [he]
          linarith
        have hdich : ∀ r u, r ≤ u → z u ≤ z r + (F u - F r) - ν * (u - r) ∨ z u ≤ F u - F r := by
          intro r u hru
          obtain ⟨u', hu', he⟩ := (hz u).1
          rcases le_total u' r with h | h
          · left
            have := (hz r).2 ⟨u', h, rfl⟩
            rw [he]
            linarith
          · right
            have h1 := (hF r u' h).1
            have h2 : 0 ≤ ν * (u - u') := mul_nonneg hν.le (by linarith)
            rw [he]; linarith
        have hup : ∀ r u, r ≤ u → z u - z r ≤ F u - F r := by
          intro r u hru
          have h2 : 0 ≤ ν * (u - r) := mul_nonneg hν.le (by linarith)
          rcases hdich r u hru with h | h
          · linarith
          · have := hz0 r; linarith
        have hzn : ∀ u ≤ 0, z u = 0 := by
          intro u hu
          refine le_antisymm ?_ (hz0 u)
          obtain ⟨u', hu', he⟩ := (hz u).1
          have h2 : 0 ≤ ν * (u - u') := mul_nonneg hν.le (by linarith)
          rw [he, hF0 u hu, hF0 u' (hu'.trans hu)]; linarith
        have hg' : LocallyIntegrable (fun θ => g θ + ν) := hg.add (locallyIntegrable_const ν)
        obtain ⟨hzAC, -, hzd, -⟩ := ac_lemma z (fun θ => g θ + ν) hg' (fun a b hab => by
          have hi : ∫ θ in a..b, (g θ + ν) = (∫ θ in a..b, g θ) + ν * (b - a) := by
            rw [intervalIntegral.integral_add (hgi a b) (by simp)]
            simp [mul_comm]
          have h2 : 0 ≤ ν * (b - a) := mul_nonneg hν.le (by linarith)
          have h3 := hF a b hab
          have h4 := hup a b hab
          have h5 := hlow a b hab
          rw [hi, abs_le]
          constructor <;> linarith)
        have hmem : ∀ u, F (u + z u / ν) - z (u + z u / ν) = F u := by
          intro u
          have hq : 0 ≤ z u / ν := div_nonneg (hz0 u) hν.le
          have hq' : ν * (u + z u / ν - u) = z u := by field_simp; ring
          have h1 := hlow u (u + z u / ν) (by linarith)
          rw [hq'] at h1
          rcases hdich u (u + z u / ν) (by linarith) with h | h
          · rw [hq'] at h; linarith
          · linarith
        refine ⟨z, fun u => F (u - τ) - z (u - τ), hz, ?_, ⟨hzn, hzAC, ?_⟩, ?_, ?_, ?_, ?_⟩
        · intro u; simp
        · filter_upwards [hFd, hzd] with u hu1 hu2 _
          split_ifs with h
          · have hzu : z u = 0 := le_antisymm h (hz0 u)
            have hmin : IsLocalMin z u := Filter.Eventually.of_forall fun r => by rw [hzu]; exact hz0 r
            have hd0 : deriv z u = 0 := hmin.deriv_eq_zero
            rw [hd0] at hu2
            have hle : deriv F u - ν ≤ 0 := by
              have hφ : HasDerivAt (fun r => F r - ν * r - z r) (deriv F u - ν * 1 - 0) u :=
                (hu1.sub ((hasDerivAt_id u).const_mul ν)).sub hu2
              have ht := hφ.tendsto_slope_zero_right
              have := le_of_tendsto (b := (0:ℝ)) ht (by
                filter_upwards [self_mem_nhdsWithin] with t ht
                have ht' : (0:ℝ) < t := ht
                have h1 := hlow u (u + t) (by linarith)
                rw [smul_eq_mul]
                refine mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht'.le) ?_
                rw [hzu] at h1 ⊢
                nlinarith)
              linarith
            rw [max_eq_right hle]
            exact hu2
          · push Not at h
            have hev : ∀ᶠ r in nhds u, z r = z u + (F r - F u) - ν * (r - u) := by
              have e1 : ∀ᶠ r in nhds u, F u - F r < z u := by
                have : ContinuousAt (fun r => F u - F r) u := by fun_prop
                exact this.eventually_lt continuousAt_const (by simpa using h)
              have e2 : ∀ᶠ r in nhds u, ν * (r - u) < z u := by
                have : ContinuousAt (fun r => ν * (r - u)) u := by fun_prop
                exact this.eventually_lt continuousAt_const (by simpa using h)
              filter_upwards [e1, e2] with r h1 h2
              rcases le_total r u with hr | hr
              · have h3 := hlow r u hr
                rcases hdich r u hr with h4 | h4
                · linarith
                · linarith
              · have h3 := hlow u r hr
                rcases hdich u r hr with h4 | h4
                · linarith
                · linarith
            have hd : HasDerivAt (fun r => z u + (F r - F u) - ν * (r - u)) (deriv F u - ν) u := by
              have := ((hu1.sub_const (F u)).const_add (z u)).sub
                (((hasDerivAt_id u).sub_const u).const_mul ν)
              rw [mul_one] at this
              exact this
            exact hd.congr_of_eventuallyEq hev
        · intro a b hab
          have h1 := hup (a - τ) (b - τ) (by linarith)
          have h2 := hlow (a - τ) (b - τ) (by linarith)
          constructor
          · simp only; linarith
          · simp only; nlinarith
        · intro u hu
          simp only
          rw [hF0 _ (by linarith), hzn _ (by linarith)]; simp
        · intro u
          have hq : 0 ≤ z u / ν := div_nonneg (hz0 u) hν.le
          refine ⟨⟨hq, ?_⟩, ?_⟩
          · simp only
            rw [show u + τ + z u / ν - τ = u + z u / ν by ring, hmem u]
          · rintro q ⟨hq0, hq1⟩
            simp only at hq1
            rw [show u + τ + q - τ = u + q by ring] at hq1
            have h1 := hlow u (u + q) (by linarith)
            rw [div_le_iff₀ hν]
            nlinarith
        · intro u
          simp only
          rw [show u + τ + z u / ν - τ = u + z u / ν by ring, hmem u]
      have E_cont : ∀ (f Φ : ℝ → ℝ) (_ : Continuous Φ)
          (_ : ∀ α β : ℝ, α ≤ β → |f β - f α| ≤ Φ β - Φ α), Continuous f := by
        clear hrm hν0 ν0 hN N arc_lemma ac_lemma limit_exists C_approx C_tel C_move C_ulim disc B_flow_add B_init B_growth cut_bound B_flowsum wf0 step_exists A_max A_bdd A_sum
        intro f Φ hΦ h
        rw [Metric.continuous_iff] at hΦ ⊢
        intro b ε hε
        obtain ⟨δ, hδ, H⟩ := hΦ b ε hε
        refine ⟨δ, hδ, fun a ha => lt_of_le_of_lt ?_ (H a ha)⟩
        rw [Real.dist_eq, Real.dist_eq]
        rcases le_total a b with hab | hab
        · have := h a b hab
          rw [abs_sub_comm (f a), abs_sub_comm (Φ a)]
          exact this.trans (le_abs_self _)
        · have := h b a hab
          exact this.trans (le_abs_self _)
      have E_inflow : ∀ (ν0 : ℝ → ℝ) (_ : IsInflowRate ν0),
          Monotone (cum ν0) ∧ Continuous (cum ν0) ∧ (∀ θ ≤ 0, cum ν0 θ = 0) ∧
          (∀ a b, ∫ θ in a..b, ν0 θ = cum ν0 b - cum ν0 a) ∧
          (∀ᵐ u, HasDerivAt (cum ν0) (ν0 u) u) := by
        clear hrm hν0 ν0 hN N E_cont arc_lemma ac_lemma limit_exists C_approx C_tel C_move C_ulim disc B_flow_add B_init B_growth cut_bound B_flowsum wf0 step_exists A_max A_bdd A_sum
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
      have E_geom : ∀ (N : QNet) (_ : N.Standing) (X : ℝ → ℝ) (_ : Monotone X)
          (_ : Continuous X) (C : ℝ) (l : ℝ → N.G.V → ℝ) (x T : ℝ → N.G.A → ℝ) (_ : 0 ≤ C)
            (_ : ∀ θ, l θ N.G.s = θ) (_ : ∀ θ ≤ 0, ∀ a, x θ a = 0)
            (_ : ∀ α β v, α ≤ β → 0 ≤ l β v - l α v ∧ l β v - l α v ≤ C * (β - α + X β - X α))
            (_ : ∀ α β a, α ≤ β → 0 ≤ x β a - x α a ∧ x β a - x α a ≤ X β - X α)
            (_ : ∀ θ v, outflow N.G (x θ) v - inflow N.G (x θ) v =
              (if v = N.G.s then X θ else 0) - (if v = N.G.t then X θ else 0))
            (_ : ∀ θ a, l θ (N.G.head a) ≤ T θ a)
            (_ : ∀ θ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l θ w = T θ a)
            (_ : ∀ α β a, α ≤ β → x α a < x β a → ∃ θ ∈ Set.Icc α β, l θ (N.G.head a) = T θ a)
            (_ : ∀ θ a, ∀ θ' ≤ θ, l θ' (N.G.tail a) + N.τ a + (x θ a - x θ' a) / N.ν a ≤ T θ a)
            (_ : ∀ θ a, ∃ θ' ≤ θ, T θ a = l θ' (N.G.tail a) + N.τ a + (x θ a - x θ' a) / N.ν a),
            (∀ v, Continuous (fun θ => l θ v)) ∧ (∀ a, Continuous (fun θ => x θ a)) ∧
            (∀ a, Continuous (fun θ => T θ a)) ∧ (∀ θ v, θ ≤ l θ v) ∧
            (∀ v, ∃ K, ∀ θ ≤ 0, l θ v ≤ θ + K) ∧
            (∀ a α β, α ≤ β → T α a + (x β a - x α a) / N.ν a ≤ T β a) ∧
            (∀ a α β, α < β → (∀ r ∈ Set.Ioc α β, x r a = x β a) → x α a = x β a) ∧
            (∀ a α β, α ≤ β → x β a - x α a ≤ N.ν a * (l β (N.G.head a) - l α (N.G.head a))) := by
        clear hrm hν0 ν0 hN N E_inflow arc_lemma ac_lemma limit_exists C_approx C_tel C_move C_ulim disc B_flow_add B_init B_growth cut_bound B_flowsum step_exists A_max A_bdd A_sum
        intro N hN X hXm hXc C l x T hC h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
        obtain ⟨hst, hν, hτ, hac, hre⟩ := hN
        have hlc : ∀ v, Continuous (fun θ => l θ v) := by
          intro v
          apply E_cont _ (fun θ => C * (θ + X θ)) (by fun_prop)
          intro α β hab
          obtain ⟨p, q⟩ := h3 α β v hab
          rw [abs_of_nonneg p]; linarith
        have hxc : ∀ a, Continuous (fun θ => x θ a) := by
          intro a
          apply E_cont _ X hXc
          intro α β hab
          obtain ⟨p, q⟩ := h4 α β a hab
          rw [abs_of_nonneg p]; linarith
        have hTm : ∀ a α β, α ≤ β → T α a + (x β a - x α a) / N.ν a ≤ T β a := by
          intro a α β hab
          obtain ⟨θ', hθ', e⟩ := h10 α a
          have := h9 β a θ' (hθ'.trans hab)
          rw [e]
          have e2 : (x β a - x θ' a) / N.ν a = (x β a - x α a) / N.ν a + (x α a - x θ' a) / N.ν a := by ring
          linarith
        have hTc : ∀ a, Continuous (fun θ => T θ a) := by
          intro a
          apply E_cont _ (fun θ => C * (θ + X θ) + X θ / N.ν a) (by fun_prop)
          intro α β hab
          have hx0 := (h4 α β a hab)
          have q1 : (x β a - x α a) / N.ν a ≤ (X β - X α) / N.ν a :=
            div_le_div_of_nonneg_right hx0.2 (hν a).le
          have q0 : 0 ≤ (x β a - x α a) / N.ν a := div_nonneg hx0.1 (hν a).le
          have q2 := hTm a α β hab
          have q3 := (hXm hab)
          rw [abs_of_nonneg (by linarith)]
          have q4 : (X β - X α) / N.ν a = X β / N.ν a - X α / N.ν a := by ring
          have q5 : 0 ≤ C * (β - α + X β - X α) := mul_nonneg hC (by linarith)
          obtain ⟨θ', hθ', e⟩ := h10 β a
          rcases le_total θ' α with h | h
          · have := h9 α a θ' h
            have e2 : (x β a - x θ' a) / N.ν a = (x β a - x α a) / N.ν a + (x α a - x θ' a) / N.ν a := by ring
            linarith
          · have w1 := h9 α a α le_rfl
            have w2 := h3 θ' β (N.G.tail a) hθ'
            have w3 := h3 α β (N.G.tail a) hab
            have w4 := h4 α θ' a h
            have e2 : (x β a - x θ' a) / N.ν a = (x β a - x α a) / N.ν a - (x θ' a - x α a) / N.ν a := by ring
            have w5 : 0 ≤ (x θ' a - x α a) / N.ν a := div_nonneg w4.1 (hν a).le
            rw [sub_self, zero_div] at w1
            linarith
        have hxJ : ∀ a α β, α < β → (∀ r ∈ Set.Ioc α β, x r a = x β a) → x α a = x β a := by
          intro a α β hab hr
          by_contra hne
          have hlt : x α a < x β a := lt_of_le_of_ne (by linarith [(h4 α β a hab.le).1]) hne
          have ev : ∀ᶠ r in nhdsWithin α (Set.Ioi α), x r a < x β a :=
            ((hxc a).continuousAt.eventually_lt continuousAt_const hlt).filter_mono nhdsWithin_le_nhds
          have ev2 : ∀ᶠ r in nhdsWithin α (Set.Ioi α), r ∈ Set.Ioc α β := Ioc_mem_nhdsGT hab
          obtain ⟨r, hr1, hr2⟩ := (ev.and ev2).exists
          exact absurd (hr r hr2) hr1.ne
        have hge : ∀ θ v, θ ≤ l θ v := by
          intro θ v
          induction v using (wf0 N ⟨hst, hν, hτ, hac, hre⟩ (l θ)).induction with
          | _ v ih =>
            by_cases hv : v = N.G.s
            · rw [hv, h1]
            · obtain ⟨a, ha, e⟩ := h7 θ v hv
              have w1 := h9 θ a θ le_rfl
              rw [sub_self, zero_div, add_zero] at w1
              have := ih (N.G.tail a) ⟨a, rfl, ha, by rw [e]; exact w1⟩
              linarith [hτ a]
        have hK : ∀ v, ∃ K, ∀ θ ≤ 0, l θ v ≤ θ + K := by
          intro v
          have hr := hre v
          unfold Reaches at hr
          induction hr with
          | refl => exact ⟨0, fun θ _ => by rw [h1]; simp⟩
          | tail _ hadj ih =>
            obtain ⟨K, hK⟩ := ih
            obtain ⟨a, ha1, ha2⟩ := hadj
            refine ⟨K + N.τ a, fun θ hθ => ?_⟩
            have w1 := h6 θ a
            obtain ⟨θ', hθ', e⟩ := h10 θ a
            rw [h2 θ hθ, h2 θ' (hθ'.trans hθ), sub_self, zero_div, add_zero] at e
            have w2 := (h3 θ' θ (N.G.tail a) hθ').1
            have w3 := hK θ hθ
            rw [ha2] at w1
            rw [ha1] at e w2
            linarith
        refine ⟨hlc, hxc, hTc, hge, hK, hTm, hxJ, ?_⟩
        intro a α β hab
        by_cases hx : x α a = x β a
        · rw [hx, sub_self]
          exact mul_nonneg (hν a).le (h3 α β _ hab).1
        · have hlt : x α a < x β a := lt_of_le_of_ne (by linarith [(h4 α β a hab).1]) hx
          let S : Set ℝ := Set.Icc α β ∩ {θ | l θ (N.G.head a) = T θ a}
          have hSc : IsCompact S := isCompact_Icc.inter_right (isClosed_eq (hlc _) (hTc a))
          have hSn : S.Nonempty := by
            obtain ⟨θ, hθ, e⟩ := h8 α β a hab hlt
            exact ⟨θ, hθ, e⟩
          obtain ⟨θ1, hθ1, hmin⟩ := hSc.exists_isLeast hSn
          obtain ⟨θ2, hθ2, hmax⟩ := hSc.exists_isGreatest hSn
          have k1 : x θ1 a ≤ x α a := by
            by_contra hc
            rw [not_le] at hc
            have hne : α ≠ θ1 := fun e => by rw [← e] at hc; exact lt_irrefl _ hc
            have hlt1 : α < θ1 := lt_of_le_of_ne hθ1.1.1 hne
            have ev : ∀ᶠ r in nhdsWithin θ1 (Set.Iio θ1), x α a < x r a :=
              (continuousAt_const.eventually_lt (hxc a).continuousAt hc).filter_mono nhdsWithin_le_nhds
            have ev2 : ∀ᶠ r in nhdsWithin θ1 (Set.Iio θ1), r ∈ Set.Ico α θ1 := Ico_mem_nhdsLT hlt1
            obtain ⟨r, hr1, hr2⟩ := (ev.and ev2).exists
            obtain ⟨θ, hθ, e⟩ := h8 α r a hr2.1 hr1
            have := hmin (a := θ) ⟨⟨hθ.1, (hθ.2.trans hr2.2.le).trans hθ1.1.2⟩, e⟩
            linarith [hθ.2, hr2.2]
          have k2 : x β a ≤ x θ2 a := by
            rcases hθ2.1.2.eq_or_lt with e | hlt2
            · rw [e]
            · refine (hxJ a θ2 β hlt2 fun r hr => ?_).ge
              by_contra hne
              have hlt3 : x r a < x β a := lt_of_le_of_ne (by linarith [(h4 r β a hr.2).1]) hne
              obtain ⟨θ, hθ, e⟩ := h8 r β a hr.2 hlt3
              have := hmax (a := θ) ⟨⟨by linarith [hθ.1, hr.1, hθ2.1.1], hθ.2⟩, e⟩
              linarith [hθ.1, hr.1]
          have k3 : θ1 ≤ θ2 := hmin hθ2
          have k4 := hTm a θ1 θ2 k3
          have e1 : l θ1 (N.G.head a) = T θ1 a := hθ1.2
          have e2 : l θ2 (N.G.head a) = T θ2 a := hθ2.2
          have k5 := (h3 α θ1 (N.G.head a) hθ1.1.1).1
          have k6 := (h3 θ2 β (N.G.head a) hθ2.1.2).1
          have k7 : (x θ2 a - x θ1 a) / N.ν a ≤ l β (N.G.head a) - l α (N.G.head a) := by linarith
          rw [div_le_iff₀ (hν a)] at k7
          linarith
      have E_walk : ∀ (N : QNet) (_ : N.Standing) (fp fm : N.G.A → ℝ → ℝ) (l : ℝ → N.G.V → ℝ)
          (T : ℝ → N.G.A → ℝ) (_ : ∀ θ, l θ N.G.s = θ)
          (_ : ∀ θ a, l θ (N.G.head a) ≤ T θ a)
          (_ : ∀ θ w, w ≠ N.G.s → ∃ a, N.G.head a = w ∧ l θ w = T θ a)
          (_ : ∀ θ a, l θ (N.G.tail a) + N.τ a ≤ T θ a)
          (_ : ∀ θ a, exitTime N fp fm a (l θ (N.G.tail a)) = T θ a)
          (_ : ∀ a, Monotone (exitTime N fp fm a)), IsEarliestTimes N fp fm l := by
        clear hrm hν0 ν0 hN N E_geom E_inflow E_cont arc_lemma ac_lemma limit_exists C_approx C_tel C_move C_ulim disc B_flow_add B_init B_growth cut_bound B_flowsum step_exists A_max A_bdd A_sum
        intro N hN fp fm l T h1 h6 h7 h9 hT hmono θ v
        have key : ∀ v, ∀ q w, IsWalk N.G v q w →
            ∃ p, IsWalk N.G N.G.s p w ∧ exitAlong N fp fm p θ = exitAlong N fp fm q (l θ v) := by
          intro v
          induction v using (wf0 N hN (l θ)).induction with
          | _ v ih =>
            intro q w hq
            by_cases hv : v = N.G.s
            · subst hv
              exact ⟨q, hq, by rw [h1]⟩
            · obtain ⟨a, ha, e⟩ := h7 θ v hv
              obtain ⟨p, hp, e2⟩ := ih (N.G.tail a) ⟨a, rfl, ha, by rw [e]; exact h9 θ a⟩ (a :: q) w
                ⟨rfl, by rw [ha]; exact hq⟩
              refine ⟨p, hp, ?_⟩
              rw [e2]
              simp only [exitAlong]
              rw [hT, e]
        have key2 : ∀ (p : List N.G.A) v w u, IsWalk N.G v p w → l θ v ≤ u →
            l θ w ≤ exitAlong N fp fm p u := by
          intro p
          induction p with
          | nil =>
            intro v w u hp hu
            have : v = w := hp
            subst this
            exact hu
          | cons a p ih =>
            intro v w u hp hu
            obtain ⟨hp1, hp2⟩ := hp
            refine ih (N.G.head a) w _ hp2 ?_
            have := hmono a hu
            rw [← hp1, hT] at this
            exact (h6 θ a).trans this
        constructor
        · obtain ⟨p, hp, e⟩ := key v [] v rfl
          exact ⟨p, hp, e.symm⟩
        · rintro r ⟨p, hp, rfl⟩
          exact key2 p _ _ _ hp (h1 θ).le
      clear hrm E_cont C_approx C_tel C_move C_ulim disc B_flow_add B_init B_growth cut_bound B_flowsum wf0 step_exists A_max A_bdd A_sum
      obtain ⟨hXm, hXc, hX0, hXi, hXd⟩ := E_inflow ν0 hν0
      generalize hXdef : cum ν0 = X at hXm hXc hX0 hXi hXd
      obtain ⟨C, l, x, T, hC, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
        limit_exists N hN X hXm hXc hX0
      obtain ⟨hlc, hxc, hTc, hge, hK, hTm, hxJ, hxl⟩ :=
        E_geom N hN X hXm hXc C l x T hC h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      have hν := hN.2.1
      have hτ := hN.2.2.1
      have hlm : ∀ v, Monotone (fun θ => l θ v) := fun v α β hab => by
        have := (h3 α β v hab).1
        simp only; linarith
      have hsurj : ∀ v, Function.Surjective (fun θ => l θ v) := by
        intro v
        refine (hlc v).surjective ?_ ?_
        · exact Filter.tendsto_atTop_mono (fun θ => hge θ v) Filter.tendsto_id
        · obtain ⟨K, hK⟩ := hK v
          refine Filter.tendsto_atBot_mono' _ ?_ (Filter.tendsto_atBot_add_const_right _ K Filter.tendsto_id)
          filter_upwards [Filter.eventually_le_atBot 0] with θ hθ using hK θ hθ
      choose σ hσ using hsurj
      simp only at hσ
      obtain ⟨Cν, hCν0, hCν⟩ : ∃ Cν : ℝ, 0 ≤ Cν ∧ ∀ a, N.ν a ≤ Cν :=
        ⟨∑ a, N.ν a, Finset.sum_nonneg fun a _ => (hν a).le, fun a =>
          Finset.single_le_sum (fun b _ => (hν b).le) (Finset.mem_univ a)⟩
      -- domination
      obtain ⟨D, hD0, hU⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ a α β, α ≤ β → x β a - x α a ≤
          D * (l β (N.G.tail a) - l α (N.G.tail a)) +
            (X (l β (N.G.tail a)) - X (l α (N.G.tail a))) := by
        refine ⟨∑ b, N.ν b, Finset.sum_nonneg fun a _ => (hν a).le, fun a α β hab => ?_⟩
        have m0 := (h3 α β (N.G.tail a) hab).1
        have m1 : X (l α (N.G.tail a)) ≤ X (l β (N.G.tail a)) := hXm (by linarith)
        have m2 : 0 ≤ ∑ b, N.ν b := Finset.sum_nonneg fun a _ => (hν a).le
        by_cases hs : N.G.tail a = N.G.s
        · have := (h4 α β a hab).2
          rw [hs] at m0 ⊢
          have := mul_nonneg m2 m0
          rw [h1, h1] at *
          linarith
        · have ha := h5 α (N.G.tail a)
          have hb := h5 β (N.G.tail a)
          rw [if_neg hs] at ha hb
          have hio : outflow N.G (x β) (N.G.tail a) - outflow N.G (x α) (N.G.tail a) ≤
              inflow N.G (x β) (N.G.tail a) - inflow N.G (x α) (N.G.tail a) := by
            have := hXm hab
            split_ifs at ha hb <;> linarith
          have ho : x β a - x α a ≤
              outflow N.G (x β) (N.G.tail a) - outflow N.G (x α) (N.G.tail a) := by
            unfold outflow
            rw [← Finset.sum_sub_distrib]
            exact Finset.single_le_sum (f := fun b => x β b - x α b) (fun b _ => (h4 α β b hab).1)
              (by simp)
          have hi : inflow N.G (x β) (N.G.tail a) - inflow N.G (x α) (N.G.tail a) ≤
              (∑ b, N.ν b) * (l β (N.G.tail a) - l α (N.G.tail a)) := by
            unfold inflow
            rw [← Finset.sum_sub_distrib, Finset.sum_mul]
            calc _ ≤ ∑ b ∈ Finset.univ.filter (fun b => N.G.head b = N.G.tail a),
                  N.ν b * (l β (N.G.tail a) - l α (N.G.tail a)) := by
                    refine Finset.sum_le_sum fun b hb => ?_
                    have hb' : N.G.head b = N.G.tail a := (Finset.mem_filter.mp hb).2
                    rw [← hb']
                    exact hxl b α β hab
              _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                  fun b _ _ => mul_nonneg (hν b).le m0
          linarith
      have hflat : ∀ a α β, l α (N.G.tail a) = l β (N.G.tail a) → x α a = x β a := by
        have : ∀ a α β, α ≤ β → l α (N.G.tail a) = l β (N.G.tail a) → x α a = x β a := by
          intro a α β hab e
          have p := hU a α β hab
          have q := (h4 α β a hab).1
          rw [e, sub_self, sub_self, mul_zero, add_zero] at p
          linarith
        intro a α β e
        rcases le_total α β with h | h
        · exact this a α β h e
        · exact (this a β α h e.symm).symm
      let F : N.G.A → ℝ → ℝ := fun a u => x (σ (N.G.tail a) u) a
      have hF : ∀ a θ, F a (l θ (N.G.tail a)) = x θ a := fun a θ => hflat a _ _ (hσ _ _)
      let g : ℝ → ℝ := fun u => D + ν0 u
      have hgL : LocallyIntegrable g (volume : Measure ℝ) := (locallyIntegrable_const D).add hν0.1
      have hgi : ∀ a b, ∫ θ in a..b, g θ = D * (b - a) + (X b - X a) := by
        intro a b
        rw [intervalIntegral.integral_add (by simp)
          ((LocallyIntegrable.integrableOn_isCompact hν0.1 isCompact_uIcc).intervalIntegrable), hXi]
        simp [mul_comm]
      have hFg : ∀ e a b, a ≤ b → 0 ≤ F e b - F e a ∧ F e b - F e a ≤ ∫ θ in a..b, g θ := by
        intro e a b hab
        rcases hab.eq_or_lt with rfl | hab
        · simp
        have hs : σ (N.G.tail e) a ≤ σ (N.G.tail e) b := by
          by_contra hc
          rw [not_le] at hc
          have := hlm (N.G.tail e) hc.le
          simp only [hσ] at this
          linarith
        have p := hU e _ _ hs
        have q := (h4 _ _ e hs).1
        rw [hσ, hσ] at p
        rw [hgi]
        exact ⟨q, p⟩
      have hF0 : ∀ e, ∀ u ≤ 0, F e u = 0 := by
        intro e u hu
        refine h2 _ ?_ e
        have := hge (σ (N.G.tail e) u) (N.G.tail e)
        rw [hσ] at this
        linarith
      choose z Fm hz1 hz2 hz3 hz4 hz5 hz6 hz7 using fun a =>
        arc_lemma (F a) g (N.ν a) (N.τ a) (hν a) (hτ a) hgL (hFg a) (hF0 a)
      have hFm : ∀ a, Monotone (F a) := fun a u v huv => by linarith [(hFg a u v huv).1]
      have hFmm : ∀ a, Monotone (Fm a) := fun a u v huv => by linarith [(hz4 a u v huv).1]
      have hacF := fun a => ac_lemma (F a) g hgL (fun u v huv => by
        rw [abs_of_nonneg (hFg a u v huv).1]; exact (hFg a u v huv).2)
      have hacFm := fun a => ac_lemma (Fm a) (fun _ => N.ν a) (locallyIntegrable_const _)
        (fun u v huv => by
          rw [abs_of_nonneg (hz4 a u v huv).1]
          simpa [mul_comm] using (hz4 a u v huv).2)
      let fp : N.G.A → ℝ → ℝ := fun a => deriv (F a)
      let fm : N.G.A → ℝ → ℝ := fun a => deriv (Fm a)
      have hcp : ∀ a, cum (fp a) = F a := by
        intro a; funext u
        have := (hacF a).2.2.2 0 u
        rw [hF0 a 0 le_rfl, sub_zero] at this
        exact this
      have hcm : ∀ a, cum (fm a) = Fm a := by
        intro a; funext u
        have := (hacFm a).2.2.2 0 u
        rw [hz5 a 0 le_rfl, sub_zero] at this
        exact this
      have hq : ∀ a, queueLen N fp fm a = z a := by
        intro a; funext u
        unfold queueLen
        rw [hcp, hcm, hz2]; ring
      have hex : ∀ a u, exitTime N fp fm a u = u + z a u / N.ν a + N.τ a := by
        intro a u
        unfold exitTime qDelay
        rw [hcp, hcm, (hz6 a u).csInf_eq]
      have hT : ∀ θ a, exitTime N fp fm a (l θ (N.G.tail a)) = T θ a := by
        intro θ a
        rw [hex]
        apply le_antisymm
        · obtain ⟨u', hu', e⟩ := (hz1 a (l θ (N.G.tail a))).1
          have hkey : ∃ θ' ≤ θ, l θ' (N.G.tail a) = u' := by
            rcases hu'.eq_or_lt with h | h
            · exact ⟨θ, le_rfl, h.symm⟩
            · refine ⟨σ (N.G.tail a) u', ?_, hσ _ _⟩
              by_contra hc
              rw [not_le] at hc
              have := hlm (N.G.tail a) hc.le
              simp only [hσ] at this
              linarith
          obtain ⟨θ', hθ', rfl⟩ := hkey
          rw [hF, hF] at e
          have := h9 θ a θ' hθ'
          rw [e, sub_div, mul_div_cancel_left₀ _ (hν a).ne']
          linarith
        · obtain ⟨θ', hθ', e⟩ := h10 θ a
          have := (hz1 a (l θ (N.G.tail a))).2 (show x θ a - x θ' a - N.ν a *
            (l θ (N.G.tail a) - l θ' (N.G.tail a)) ∈ _ from
            ⟨l θ' (N.G.tail a), hlm _ hθ', by rw [hF, hF]⟩)
          have h' := div_le_div_of_nonneg_right this (hν a).le
          rw [sub_div, mul_div_cancel_left₀ _ (hν a).ne'] at h'
          rw [e]; linarith
      have hmono : ∀ a, Monotone (exitTime N fp fm a) := by
        intro a u r hur
        rw [hex, hex]
        obtain ⟨u', hu', e⟩ := (hz1 a u).1
        have := (hz1 a r).2 (show F a r - F a u' - N.ν a * (r - u') ∈ _ from ⟨u', hu'.trans hur, rfl⟩)
        have k := hFm a hur
        have h' : z a u / N.ν a ≤ (z a r + N.ν a * (r - u)) / N.ν a :=
          div_le_div_of_nonneg_right (by rw [e]; nlinarith) (hν a).le
        rw [add_div, mul_div_cancel_left₀ _ (hν a).ne'] at h'
        linarith
      have h9' : ∀ θ a, l θ (N.G.tail a) + N.τ a ≤ T θ a := by
        intro θ a
        have := h9 θ a θ le_rfl
        rwa [sub_self, zero_div, add_zero] at this
      have hFT : ∀ a θ, Fm a (T θ a) = x θ a := by
        intro a θ
        have := hz7 a (l θ (N.G.tail a))
        rw [hF] at this
        rw [← this, ← hT, hex]
        congr 1; ring
      have hH : ∀ a θ, Fm a (l θ (N.G.head a)) = x θ a := by
        intro a θ
        apply le_antisymm
        · rw [← hFT a θ]; exact hFmm a (h6 θ a)
        · -- last time with T ≤ l θ head
          obtain ⟨K, hK⟩ := hK (N.G.tail a)
          let θ0 : ℝ := min (min 0 θ) (l θ (N.G.head a) - K - N.τ a)
          have hθ00 : θ0 ≤ 0 := (min_le_left _ _).trans (min_le_left _ _)
          have hθ0θ : θ0 ≤ θ := (min_le_left _ _).trans (min_le_right _ _)
          have hθ0l : θ0 ≤ l θ (N.G.head a) - K - N.τ a := min_le_right _ _
          let S : Set ℝ := Set.Icc θ0 θ ∩ {r | T r a ≤ l θ (N.G.head a)}
          have hSc : IsCompact S := isCompact_Icc.inter_right (isClosed_le (hTc a) continuous_const)
          have hSn : S.Nonempty := by
            refine ⟨θ0, ⟨le_rfl, hθ0θ⟩, ?_⟩
            obtain ⟨θ', hθ', e⟩ := h10 θ0 a
            rw [h2 θ0 hθ00, h2 θ' (hθ'.trans hθ00), sub_self, zero_div, add_zero] at e
            have w2 : l θ' (N.G.tail a) ≤ l θ0 (N.G.tail a) := hlm _ hθ'
            have w3 := hK θ0 hθ00
            show T θ0 a ≤ _
            linarith
          obtain ⟨θ1, hθ1, hmax⟩ := hSc.exists_isGreatest hSn
          have hx1 : x θ1 a = x θ a := by
            rcases hθ1.1.2.eq_or_lt with h | h
            · rw [h]
            · refine hxJ a θ1 θ h fun r hr => ?_
              by_contra hne
              have hlt3 : x r a < x θ a := lt_of_le_of_ne (by linarith [(h4 r θ a hr.2).1]) hne
              obtain ⟨θ2, hθ2, e⟩ := h8 r θ a hr.2 hlt3
              have hl2 : l θ2 (N.G.head a) ≤ l θ (N.G.head a) := hlm _ hθ2.2
              have := hmax (a := θ2) ⟨⟨by linarith [hθ2.1, hr.1, hθ1.1.1], hθ2.2⟩, by
                show T θ2 a ≤ _
                rw [← e]; exact hl2⟩
              linarith [hθ2.1, hr.1]
          rw [← hx1, ← hFT a θ1]
          exact hFmm a hθ1.2
      have hcons : ∀ v, v ≠ N.G.t → ∀ u, outflow N.G (fun a => F a u) v - inflow N.G (fun a => Fm a u) v
          = if v = N.G.s then X u else 0 := by
        intro v hv u
        have := h5 (σ v u) v
        rw [if_neg hv, sub_zero] at this
        have e1 : outflow N.G (fun a => F a u) v = outflow N.G (x (σ v u)) v := by
          unfold outflow
          refine Finset.sum_congr rfl fun a ha => ?_
          have ha' : N.G.tail a = v := (Finset.mem_filter.mp ha).2
          rw [← hF a, ha', hσ]
        have e2 : inflow N.G (fun a => Fm a u) v = inflow N.G (x (σ v u)) v := by
          unfold inflow
          refine Finset.sum_congr rfl fun a ha => ?_
          have ha' : N.G.head a = v := (Finset.mem_filter.mp ha).2
          rw [← hH a, ha', hσ]
        rw [e1, e2, this]
        by_cases hs : v = N.G.s
        · subst hs
          have : σ N.G.s u = u := by rw [← h1 (σ N.G.s u)]; exact hσ _ _
          rw [this]
        · rw [if_neg hs, if_neg hs]
      have hderivF : ∀ᵐ u, ∀ a, HasDerivAt (F a) (fp a u) u := ae_all_iff.mpr fun a => (hacF a).2.2.1
      have hderivFm : ∀ᵐ u, ∀ a, HasDerivAt (Fm a) (fm a u) u := ae_all_iff.mpr fun a => (hacFm a).2.2.1
      refine ⟨fp, fm, l, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · intro a
        refine ⟨fun u => (hFm a).deriv_nonneg, fun u => (hFmm a).deriv_nonneg, (hacF a).2.1,
          (hacFm a).2.1, Filter.Eventually.of_forall fun u hu => ?_,
          Filter.Eventually.of_forall fun u hu => ?_⟩
        · have : F a =ᶠ[nhds u] fun _ => 0 := by
            filter_upwards [Iio_mem_nhds hu] with r hr using hF0 a r (le_of_lt hr)
          show deriv (F a) u = 0
          rw [this.deriv_eq]; simp
        · have : Fm a =ᶠ[nhds u] fun _ => 0 := by
            filter_upwards [Iio_mem_nhds hu] with r hr using hz5 a r (le_of_lt hr)
          show deriv (Fm a) u = 0
          rw [this.deriv_eq]; simp
      · intro a
        rw [hq]
        exact hz3 a
      · filter_upwards [hderivF, hderivFm, hXd] with u hu1 hu2 hu3 v hv
        have d1 : HasDerivAt (fun r => outflow N.G (fun a => F a r) v - inflow N.G (fun a => Fm a r) v)
            (outflow N.G (fun a => fp a u) v - inflow N.G (fun a => fm a u) v) u := by
          unfold outflow inflow
          exact (HasDerivAt.fun_sum fun a _ => hu1 a).sub (HasDerivAt.fun_sum fun a _ => hu2 a)
        have d2 : HasDerivAt (fun r => outflow N.G (fun a => F a r) v - inflow N.G (fun a => Fm a r) v)
            (if v = N.G.s then ν0 u else 0) u := by
          rw [funext (hcons v hv)]
          split_ifs
          · exact hu3
          · exact hasDerivAt_const _ _
        exact d1.unique d2
      · exact E_walk N hN fp fm l T h1 h6 h7 h9' hT hmono
      · intro a
        have hcount : (Set.range fun q : ℚ => l (q : ℝ) (N.G.tail a)).Countable :=
          Set.countable_range _
        filter_upwards [(hacF a).2.2.1, hcount.ae_notMem volume] with u hu hur
        rintro ⟨θ, rfl, hina⟩
        unfold IsActive at hina
        rw [hT] at hina
        have hlt : l θ (N.G.head a) < T θ a := lt_of_le_of_ne (h6 θ a) hina
        have hnb : ∀ᶠ r in nhds θ, l r (N.G.head a) < T r a :=
          (hlc _).continuousAt.eventually_lt (hTc a).continuousAt hlt
        obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnb
        have hconst : ∀ α β, α ≤ β → θ - δ < α → β < θ + δ → x α a = x β a := by
          intro α β hab hα hβ
          by_contra hne
          obtain ⟨r, hr, e⟩ := h8 α β a hab (lt_of_le_of_ne (by linarith [(h4 α β a hab).1]) hne)
          have := hball (y := r) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2])
          exact this.ne e
        show deriv (F a) (l θ (N.G.tail a)) = 0
        by_cases hR : ∃ r, θ < r ∧ r < θ + δ ∧ l θ (N.G.tail a) < l r (N.G.tail a)
        · obtain ⟨r, hr1, hr2, hr3⟩ := hR
          have hw : HasDerivWithinAt (F a) 0 (Set.Icc (l θ (N.G.tail a)) (l r (N.G.tail a)))
              (l θ (N.G.tail a)) := by
            refine (hasDerivWithinAt_const _ _ (F a (l θ (N.G.tail a)))).congr ?_ rfl
            intro y hy
            apply le_antisymm _ (hFm a hy.1)
            refine (hFm a hy.2).trans ?_
            rw [hF, hF]
            exact (hconst θ r hr1.le (by linarith) hr2).ge
          exact (uniqueDiffOn_Icc hr3 _ ⟨le_rfl, hr3.le⟩).eq_deriv _ hu.hasDerivWithinAt hw
        · by_cases hL : ∃ r, r < θ ∧ θ - δ < r ∧ l r (N.G.tail a) < l θ (N.G.tail a)
          · obtain ⟨r, hr1, hr2, hr3⟩ := hL
            have hw : HasDerivWithinAt (F a) 0 (Set.Icc (l r (N.G.tail a)) (l θ (N.G.tail a)))
                (l θ (N.G.tail a)) := by
              refine (hasDerivWithinAt_const _ _ (F a (l θ (N.G.tail a)))).congr ?_ rfl
              intro y hy
              apply le_antisymm (hFm a hy.2)
              refine le_trans ?_ (hFm a hy.1)
              rw [hF, hF]
              exact (hconst r θ hr1.le hr2 (by linarith)).ge
            exact (uniqueDiffOn_Icc hr3 _ ⟨hr3.le, le_rfl⟩).eq_deriv _ hu.hasDerivWithinAt hw
          · exfalso
            obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show θ < θ + δ by linarith)
            apply hur
            refine ⟨q, ?_⟩
            apply le_antisymm
            · by_contra hc
              rw [not_le] at hc
              exact hR ⟨q, hq1, hq2, hc⟩
            · exact hlm _ hq1.le
