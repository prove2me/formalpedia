-- Prove2me | solution 1 for SRAudit.TwoPhase.Supplement.proposition_C_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:04.783101+00:00
-- url     : https://prove2.me/submissions/e8fd1964-e2f6-4f58-8b7f-c88bed661e0e

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

open SRAudit
open SRAudit.TwoPhase
open SRAudit.TwoPhase.Supplement

open SRAudit.TwoPhase

theorem solution {ι : Type} [DecidableEq ι] (E : Demand) (hE : E.Standing) :
    -- (a) strict concavity of `πj` in supplier `j`'s own strategy `sj`
    (∀ (g : Network ι), WellFormedNet g → ∀ j ∈ g.S2, ∀ s : ι → Firm → ℝ,
      StrictConcaveOn ℝ {y : Firm → ℝ | ∀ i, ¬ (i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab) → y i = 0}
        (fun y => tier2Payoff E g (Function.update s j y) j)) ∧
    -- (b) existence and uniqueness of the equilibrium of `P2`, for every capacity `M > 0`
    (∀ (M : ℝ), 0 < M → ∀ g : Network ι, WellFormedNet g → ∃! s : ι → Firm → ℝ, IsTier2Eq E g M s) ∧
    -- (c) the partial derivatives (C.12) and (C.13)
    (∀ (g : Network ι), WellFormedNet g → ∀ s : ι → Firm → ℝ, ∀ i ∈ g.T1,
      (∀ j ∈ g.excl i,
        HasDerivAt (fun t => tier2Payoff E g (Function.update s j (Function.update (s j) i t)) j)
          (-4 * E.β * s j i +
            (E.α - E.vT - 4 * E.β * ∑ j' ∈ g.excl i ∪ g.Sab, s j' i -
              2 * E.β * ∑ i' ∈ g.T1.erase i, ∑ j' ∈ g.excl i' ∪ g.Sab, s j' i'))
          (s j i)) ∧
      (∀ j ∈ g.Sab,
        HasDerivAt (fun t => tier2Payoff E g (Function.update s j (Function.update (s j) i t)) j)
          (-4 * E.β * s j i +
            (E.α - E.vT - 4 * E.β * ∑ j' ∈ g.excl i ∪ g.Sab, s j' i -
              2 * E.β * ∑ i' ∈ g.T1.erase i, ∑ j' ∈ g.excl i' ∪ g.Sab, s j' i') -
            2 * E.β * ∑ i' ∈ g.T1.erase i, s j i')
          (s j i))) := by
            classical
            have hβ : 0 < E.β := hE.1
            have quad (a b x : ℝ) (hb : 0 < b) :
                (∀ y : ℝ, (a - b * y) * y ≤ (a - b * x) * x) ↔ a = 2 * b * x := by
              constructor
              · intro h
                have hd : HasDerivAt (fun y : ℝ => (a - b * y) * y)
                    ((a - b * x) - b * x) x := by
                  convert (((hasDerivAt_const x a).sub ((hasDerivAt_id x).const_mul b)).mul
                    (hasDerivAt_id x)) using 1 <;> first | rfl | (simp only [Pi.sub_apply, id_eq]; ring)
                have hz := (show IsLocalMax (fun y : ℝ => (a - b * y) * y) x from
                  Filter.Eventually.of_forall h).hasDerivAt_eq_zero hd
                linarith
              · intro h y
                rw [h]
                nlinarith [mul_nonneg (le_of_lt hb) (sq_nonneg (y-x))]
            have inv1 (q : ℝ) : invDemand1 E q = E.α - E.v0 - 2 * E.β * q := by
              have hc (p : ℝ) : IsBuyerOptimal E p q ↔ p = E.α - E.v0 - 2 * E.β * q := by
                unfold IsBuyerOptimal buyerProfit
                have he : (fun y : ℝ => (E.α - E.β * y - E.v0 - p) * y) =
                    (fun y : ℝ => ((E.α - E.v0 - p) - E.β * y) * y) := by funext; ring
                simp_rw [show ∀ y : ℝ, (E.α - E.β * y - E.v0 - p) * y =
                  ((E.α - E.v0 - p) - E.β * y) * y from fun y => by ring]
                rw [quad _ _ _ hβ]
                constructor <;> intro h <;> linarith
              have hu : ∃! p : ℝ, IsBuyerOptimal E p q :=
                ⟨_, (hc _).2 rfl, fun p hp => (hc p).1 hp⟩
              unfold invDemand1
              rw [dif_pos hu]
              exact (hc _).1 hu.exists.choose_spec
            have inv2 (g : Network ι) (q : Firm → ℝ) (hq : ∀ x, x ∉ g.T1 → q x = 0)
                (i : Firm) (hi : i ∈ g.T1) :
                invDemand2 E g q i = E.α - E.v0 - E.v1 - 4 * E.β * q i -
                  2 * E.β * ∑ k ∈ g.T1.erase i, q k := by
              let p : Firm → ℝ := fun i => if i ∈ g.T1 then
                E.α - E.v0 - E.v1 - 4 * E.β * q i - 2 * E.β * ∑ k ∈ g.T1.erase i, q k else 0
              have he (p' : Firm → ℝ) :
                  ((∀ x, x ∉ g.T1 → p' x = 0) ∧ IsTier1Eq E g p' q) ↔ p' = p := by
                have hf (i : Firm) (hi : i ∈ g.T1) (y : ℝ) :
                    tier1Payoff E g p' (Function.update q i y) i =
                    ((E.α - E.v0 - E.v1 - p' i - 2 * E.β * ∑ k ∈ g.T1.erase i, q k) -
                      (2 * E.β) * y) * y := by
                  unfold tier1Payoff
                  rw [inv1, ← Finset.add_sum_erase _ _ hi]
                  simp only [Function.update_self, Finset.sdiff_singleton_eq_erase]
                  have hh : ∑ k ∈ g.T1.erase i, Function.update q i y k = ∑ k ∈ g.T1.erase i, q k := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    exact Function.update_of_ne (Finset.ne_of_mem_erase hk) _ _
                  rw [hh]
                  ring
                constructor
                · rintro ⟨hp', _, hbest⟩
                  funext i
                  by_cases hi : i ∈ g.T1
                  · have hb := hbest i hi
                    have hh : tier1Payoff E g p' q i = tier1Payoff E g p' (Function.update q i (q i)) i := by
                      rw [Function.update_eq_self]
                    rw [hh] at hb
                    simp_rw [hf i hi] at hb
                    have hz := (quad _ _ _ (by positivity : 0 < 2 * E.β)).1 hb
                    simp only [p, if_pos hi]
                    linarith
                  · simp [p, hi, hp' i hi]
                · intro hp'
                  subst p'
                  refine ⟨?_, hq, ?_⟩
                  · intro x hx; simp [p, hx]
                  · intro i hi y
                    have hh : tier1Payoff E g p q i = tier1Payoff E g p (Function.update q i (q i)) i := by
                      rw [Function.update_eq_self]
                    rw [hh, hf i hi y, hf i hi (q i)]
                    apply (quad _ _ _ (by positivity : 0 < 2 * E.β)).2
                    simp only [p, if_pos hi]
                    ring
              have hu : ∃! p' : Firm → ℝ, (∀ x, x ∉ g.T1 → p' x = 0) ∧ IsTier1Eq E g p' q :=
                ⟨p, (he p).2 rfl, fun p' hp' => (he p').1 hp'⟩
              unfold invDemand2
              rw [dif_pos hu, (he _).1 hu.exists.choose_spec]
              simp [p, hi]
            have payoff (g : Network ι) (s : ι → Firm → ℝ) (j : ι) :
                tier2Payoff E g s j = ∑ i ∈ g.T1.filter (fun i => j ∈ g.excl i ∪ g.Sab),
                  (E.α - E.vT - 4 * E.β * tier1Qty g s i -
                    2 * E.β * ∑ k ∈ g.T1.erase i, tier1Qty g s k) * s j i := by
              unfold tier2Payoff
              apply Finset.sum_congr rfl
              intro i hi
              rw [inv2 g _ (by intro x hx; simp [tier1Qty, hx]) i (Finset.mem_filter.mp hi).1]
              unfold Demand.vT
              ring
            have dq (c l q t : ℝ) : HasDerivAt (fun z : ℝ => c+l*z+q*z^2) (l+2*q*t) t := by
              convert ((hasDerivAt_const t c).add ((hasDerivAt_id t).const_mul l)).add
                ((hasDerivAt_pow 2 t).const_mul q) using 1 <;> first | rfl | (norm_num; ring) | (funext z; dsimp; ring)
            have finite_game (J : Type) [Fintype J] [DecidableEq J]
                (C : J → Firm → Set ℝ) (hC : ∀ j i, IsCompact (C j i))
                (hcv : ∀ j i, Convex ℝ (C j i)) (h0 : ∀ j i, 0 ∈ C j i) :
                ∃! x : J → Firm → ℝ,
                  (∀ j i, x j i ∈ C j i) ∧
                  ∀ j y, (∀ i, y i ∈ C j i) →
                    ((E.α-E.vT) * (y .a+y .b) - 2*E.β *
                      (2*((∑ k, Function.update x j y k .a))*y .a +
                        (∑ k, Function.update x j y k .a)*y .b +
                        (∑ k, Function.update x j y k .b)*y .a +
                        2*(∑ k, Function.update x j y k .b)*y .b)) ≤
                    ((E.α-E.vT) * (x j .a+x j .b) - 2*E.β *
                      (2*(∑ k, x k .a)*x j .a + (∑ k, x k .a)*x j .b +
                        (∑ k, x k .b)*x j .a + 2*(∑ k, x k .b)*x j .b)) := by
              let A := E.α-E.vT
              let B := E.β
              let H (u v : Firm → ℝ) :=
                2*u .a*v .a+u .a*v .b+u .b*v .a+2*u .b*v .b
              let T (u : Firm → ℝ) := u .a+u .b
              let Q (x : J → Firm → ℝ) (i : Firm) := ∑ j, x j i
              let F (x : J → Firm → ℝ) (j : J) := A*T (x j)-2*B*H (Q x) (x j)
              let P (x : J → Firm → ℝ) := A*T (Q x)-B*(H (Q x) (Q x)+∑ j, H (x j) (x j))
              let K : Set (J → Firm → ℝ) := {x | ∀ j i, x j i ∈ C j i}
              have q_up (x : J → Firm → ℝ) (j : J) (y : Firm → ℝ) :
                  Q (Function.update x j y) = Q x - x j + y := by
                funext i
                have hh : (fun k => Function.update x j y k i) =
                    Function.update (fun k => x k i) j (y i) := by
                  funext k; by_cases hk : k=j <;> simp [hk]
                simp only [Q, Pi.add_apply, Pi.sub_apply, hh]
                rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
                simp only [Finset.sdiff_singleton_eq_erase]
                rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
                ring
              have p_up (x : J → Firm → ℝ) (j : J) (y : Firm → ℝ) :
                  P (Function.update x j y)-P x = F (Function.update x j y) j-F x j := by
                have hh : (fun k => H (Function.update x j y k) (Function.update x j y k)) =
                    Function.update (fun k => H (x k) (x k)) j (H y y) := by
                  funext k; by_cases hk : k=j <;> simp [hk]
                simp only [P, F, q_up, Function.update_self, hh]
                rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
                simp only [Finset.sdiff_singleton_eq_erase]
                rw [← Finset.add_sum_erase Finset.univ (fun k => H (x k) (x k)) (Finset.mem_univ j)]
                dsimp [H, T]
                ring
              have hcK : IsCompact K :=
                isCompact_pi_infinite (fun j => isCompact_pi_infinite (hC j))
              have hneK : K.Nonempty := ⟨0, h0⟩
              have hcont : Continuous P := by
                dsimp [P, H, T, Q]
                fun_prop
              obtain ⟨x, hx, hmax⟩ := hcK.exists_isMaxOn hneK hcont.continuousOn
              have heqx : (∀ j i, x j i ∈ C j i) ∧
                  ∀ j y, (∀ i, y i ∈ C j i) → F (Function.update x j y) j ≤ F x j := by
                refine ⟨hx, ?_⟩
                intro j y hy
                have hu : Function.update x j y ∈ K := by
                  intro k i
                  by_cases hk : k=j
                  · simpa [hk] using hy i
                  · simpa [Function.update_of_ne hk] using hx k i
                have hm : P (Function.update x j y) ≤ P x := hmax hu
                have hp := p_up x j y
                linarith
              suffices hg : ∃! x, (∀ j i, x j i ∈ C j i) ∧
                  ∀ j y, (∀ i, y i ∈ C j i) → F (Function.update x j y) j ≤ F x j by
                simpa only [F, T, H, Q, A, B, Function.update_self] using hg
              refine ⟨x, heqx, ?_⟩
              intro z hz
              have first_order (w : J → Firm → ℝ)
                  (hw : (∀ j i, w j i ∈ C j i) ∧
                    ∀ j y, (∀ i, y i ∈ C j i) → F (Function.update w j y) j ≤ F w j)
                  (v : J → Firm → ℝ) (hv : ∀ j i, v j i ∈ C j i) (j : J) :
                  A*T (v j-w j)-2*B*(H (Q w) (v j-w j)+H (w j) (v j-w j)) ≤ 0 := by
                let d := v j-w j
                let f (t : ℝ) := F (Function.update w j (w j+t • d)) j
                have hm : IsMaxOn f (Set.Icc 0 1) 0 := by
                  intro t ht
                  have hy : ∀ i, (w j+t • d) i ∈ C j i := by
                    intro i
                    have hi := hcv j i (hw.1 j i) (hv j i) (by linarith [ht.2] : 0 ≤ 1-t) ht.1 (by ring : (1-t)+t=1)
                    convert hi using 1
                    simp only [d, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
                    ring
                  simpa [f] using hw.2 j _ hy
                let L := A*T d-2*B*(H (Q w) d+H (w j) d)
                have hf : f = fun t => F w j+L*t+(-2*B*H d d)*t^2 := by
                  funext t
                  dsimp [f, F]
                  rw [q_up]
                  simp only [Function.update_self]
                  dsimp [L, H, T]
                  try simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
                  ring
                have hd : HasDerivAt f L 0 := by
                  rw [hf]
                  convert dq (F w j) L (-2*B*H d d) 0 using 1 <;> ring
                have ht : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
                  simpa using (sub_mem_posTangentConeAt_of_segment_subset
                    (show segment ℝ (0 : ℝ) 1 ⊆ Set.Icc 0 1 by rw [segment_eq_Icc (by norm_num)]))
                have hn := hm.localize.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt ht
                simpa [ContinuousLinearMap.toSpanSingleton_apply, L, d] using hn
              have hH (u : Firm → ℝ) : 0 ≤ H u u := by
                dsimp [H]
                nlinarith [sq_nonneg (u .a), sq_nonneg (u .b), sq_nonneg (u .a+u .b)]
              have sumH (u : Firm → ℝ) (v : J → Firm → ℝ) :
                  ∑ j, H u (v j) = H u (Q v) := by
                dsimp [H, Q]
                simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
              have hs : 2*B*(H (Q z-Q x) (Q z-Q x)+∑ j, H (z j-x j) (z j-x j)) ≤ 0 := by
                have hi (j : J) := add_nonpos (first_order x heqx z hz.1 j) (first_order z hz x heqx.1 j)
                have he (j : J) :
                    (A*T (z j-x j)-2*B*(H (Q x) (z j-x j)+H (x j) (z j-x j))) +
                    (A*T (x j-z j)-2*B*(H (Q z) (x j-z j)+H (z j) (x j-z j))) =
                      2*B*(H (Q z-Q x) (z j-x j)+H (z j-x j) (z j-x j)) := by
                  dsimp [H, T]; ring
                simp_rw [he] at hi
                have hh := Finset.sum_nonpos (s := Finset.univ) (fun j _ => hi j)
                rw [← Finset.mul_sum, Finset.sum_add_distrib, sumH] at hh
                have hq : Q (fun j => z j-x j) = Q z-Q x := by
                  ext i; simp [Q, Finset.sum_sub_distrib]
                rwa [hq] at hh
              have hsum : ∑ j, H (z j-x j) (z j-x j) ≤ 0 := by
                have hn := hH (Q z-Q x)
                have hb : 0 < B := hβ
                nlinarith
              funext j i
              have hj : H (z j-x j) (z j-x j) ≤ 0 :=
                (Finset.single_le_sum (fun k _ => hH (z k-x k)) (Finset.mem_univ j)).trans hsum
              dsimp [H] at hj
              try simp only [Pi.sub_apply] at hj
              have ha := sq_nonneg (z j .a-x j .a+ (z j .b-x j .b))
              have hb := sq_nonneg (z j .a-x j .a)
              have hc := sq_nonneg (z j .b-x j .b)
              cases i <;> nlinarith
            have qother (g : Network ι) (s : ι → Firm → ℝ) (i : Firm) :
                (∑ k ∈ g.T1.erase i, tier1Qty g s k) = tier1Qty g s (otherFirm i) := by
              have he : g.T1.erase i = if otherFirm i ∈ g.T1 then {otherFirm i} else ∅ := by
                cases i <;> dsimp [otherFirm] <;> split_ifs with hh <;> ext k <;> cases k <;> simp [hh]
              rw [he]
              split_ifs with hi
              · simp
              · simp [tier1Qty, hi]
            have norm_pay (g : Network ι) (s : ι → Firm → ℝ) (j : ι)
                (hs : ∀ i, ¬ (i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab) → s j i = 0) :
                tier2Payoff E g s j =
                  (E.α-E.vT)*(s j .a+s j .b)-2*E.β*
                    (2*tier1Qty g s .a*s j .a+tier1Qty g s .a*s j .b+
                      tier1Qty g s .b*s j .a+2*tier1Qty g s .b*s j .b) := by
              rw [payoff]
              simp_rw [qother]
              have he : (∑ i ∈ g.T1.filter (fun i => j ∈ g.excl i ∪ g.Sab),
                  (E.α-E.vT-4*E.β*tier1Qty g s i-2*E.β*tier1Qty g s (otherFirm i))*s j i) =
                  ∑ i : Firm, (E.α-E.vT-4*E.β*tier1Qty g s i-2*E.β*tier1Qty g s (otherFirm i))*s j i := by
                apply Finset.sum_subset (Finset.subset_univ _)
                intro i _ hi
                rw [hs i (by simpa using hi), mul_zero]
              rw [he]
              simp only [show (Finset.univ : Finset Firm) = {.a, .b} from rfl,
                Finset.sum_insert, Finset.mem_singleton, reduceCtorEq,
                not_false_eq_true, Finset.sum_singleton, otherFirm]
              ring
            have link_sub (g : Network ι) (i : Firm) : g.excl i ∪ g.Sab ⊆ g.S2 := by
              cases i <;> intro j hj <;> simp only [Network.excl, Network.S2, Finset.mem_union] at * <;> tauto
            have qty_norm (g : Network ι) (s : ι → Firm → ℝ)
                (hs : ∀ j i, ¬ (i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab) → s j i = 0) (i : Firm) :
                tier1Qty g s i = ∑ j ∈ g.S2, s j i := by
              by_cases hi : i ∈ g.T1
              · simp only [tier1Qty, if_pos hi]
                apply Finset.sum_subset (link_sub g i)
                intro j _ hj
                exact hs j i (by tauto)
              · simp only [tier1Qty, if_neg hi]
                symm
                apply Finset.sum_eq_zero
                intro j _
                exact hs j i (by tauto)
            have qty_up (g : Network ι) (s : ι → Firm → ℝ) (j : ι) (y : Firm → ℝ) (i : Firm) :
                tier1Qty g (Function.update s j y) i = tier1Qty g s i +
                  if i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab then y i-s j i else 0 := by
              have hh : (fun k => Function.update s j y k i) =
                  Function.update (fun k => s k i) j (y i) := by
                ext k; by_cases hk : k=j <;> simp [hk]
              by_cases hi : i ∈ g.T1
              · simp only [tier1Qty, if_pos hi, hh]
                by_cases hj : j ∈ g.excl i ∪ g.Sab
                · rw [if_pos ⟨hi, hj⟩, Finset.sum_update_of_mem hj]
                  simp only [Finset.sdiff_singleton_eq_erase]
                  rw [← Finset.add_sum_erase _ _ hj]
                  ring
                · simp [hj, Finset.sum_update_of_notMem hj]
              · simp [tier1Qty, hi]
            have equilibrium (M : ℝ) (hM : 0 < M) (g : Network ι) :
                ∃! s : ι → Firm → ℝ, IsTier2Eq E g M s := by
              let J := ↥g.S2
              let C (j : J) (i : Firm) : Set ℝ :=
                if i ∈ g.T1 ∧ j.val ∈ g.excl i ∪ g.Sab then Set.Icc 0 M else {0}
              let R (s : ι → Firm → ℝ) (j : J) := s j.val
              let X (x : J → Firm → ℝ) (j : ι) : Firm → ℝ :=
                if hj : j ∈ g.S2 then x ⟨j, hj⟩ else 0
              let F (x : J → Firm → ℝ) (j : J) :=
                (E.α-E.vT)*(x j .a+x j .b)-2*E.β*
                  (2*(∑ k, x k .a)*x j .a+(∑ k, x k .a)*x j .b+
                    (∑ k, x k .b)*x j .a+2*(∑ k, x k .b)*x j .b)
              have hxR (x : J → Firm → ℝ) : R (X x) = x := by
                funext j; simp [R, X, j.property]
              have hX (x : J → Firm → ℝ) (hx : ∀ j i, x j i ∈ C j i) : Feasible2 g M (X x) := by
                intro j i
                by_cases hj : j ∈ g.S2
                · have hh := hx ⟨j, hj⟩ i
                  dsimp [C] at hh
                  simp only [X, dif_pos hj]
                  constructor
                  · intro hl
                    rw [if_pos hl] at hh
                    exact hh
                  · intro hl
                    rw [if_neg hl] at hh
                    exact hh
                · simp only [X, dif_neg hj, Pi.zero_apply]
                  exact ⟨fun _ => ⟨le_rfl, hM.le⟩, fun _ => by simp⟩
              have hR (s : ι → Firm → ℝ) (hs : Feasible2 g M s) : ∀ j i, R s j i ∈ C j i := by
                intro j i
                dsimp [R, C]
                split_ifs with hl
                · exact (hs j.val i).1 hl
                · exact (hs j.val i).2 hl
              have hXR (s : ι → Firm → ℝ) (hs : Feasible2 g M s) : X (R s) = s := by
                funext j i
                by_cases hj : j ∈ g.S2
                · simp [X, R, hj]
                · have hz := (hs j i).2 (fun h => hj (link_sub g i h.2))
                  simp [X, hj, hz]
              have pR (s : ι → Firm → ℝ) (hs : Feasible2 g M s) (j : J) :
                  tier2Payoff E g s j.val = F (R s) j := by
                rw [norm_pay g s j.val (fun i => (hs j.val i).2)]
                have hq (i : Firm) : tier1Qty g s i = ∑ k : J, R s k i := by
                  rw [qty_norm g s (fun j i => (hs j i).2)]
                  exact (Finset.sum_coe_sort g.S2 (fun k => s k i)).symm
                rw [hq, hq]
              have hRU (s : ι → Firm → ℝ) (j : J) (y : Firm → ℝ) :
                  R (Function.update s j.val y) = Function.update (R s) j y := by
                ext k i
                by_cases hk : k=j
                · subst k; simp [R]
                · have hne : k.val ≠ j.val := fun h => hk (Subtype.ext h)
                  simp [R, Function.update_of_ne hk, Function.update_of_ne hne]
              have hfU (s : ι → Firm → ℝ) (hs : Feasible2 g M s) (j : J)
                  (y : Firm → ℝ) (hy : ∀ i, y i ∈ C j i) :
                  Feasible2 g M (Function.update s j.val y) := by
                rw [← hXR s hs]
                have he : Function.update (X (R s)) j.val y = X (Function.update (R s) j y) := by
                  ext k i
                  by_cases hk : k=j.val
                  · subst k; simp [X, j.property]
                  · by_cases hmem : k ∈ g.S2
                    · have hne : (⟨k,hmem⟩ : J) ≠ j := fun h => hk (congrArg Subtype.val h)
                      simp [X, hmem, Function.update_of_ne hk, Function.update_of_ne hne]
                    · simp [X, hmem, Function.update_of_ne hk]
                rw [he]
                apply hX
                intro k i
                by_cases hk : k=j
                · simpa [hk] using hy i
                · simpa [Function.update_of_ne hk] using hR s hs k i
              have hcx : ∀ j i, IsCompact (C j i) := by
                intro j i; dsimp [C]; split_ifs <;> first | exact isCompact_Icc | exact isCompact_singleton
              have hcv : ∀ j i, Convex ℝ (C j i) := by
                intro j i; dsimp [C]; split_ifs <;> first | exact convex_Icc _ _ | exact convex_singleton _
              have hc0 : ∀ j i, 0 ∈ C j i := by
                intro j i; dsimp [C]; split_ifs <;> simp [hM.le]
              have hg := finite_game J C hcx hcv hc0
              have hg' : ∃! x, (∀ j i, x j i ∈ C j i) ∧
                  ∀ j y, (∀ i, y i ∈ C j i) → F (Function.update x j y) j ≤ F x j := by
                simpa only [F, Function.update_self] using hg
              obtain ⟨x, hx, huniq⟩ := hg'
              have hs := hX x hx.1
              have hseq : IsTier2Eq E g M (X x) := by
                refine ⟨hs, ?_⟩
                intro j hj s' hs' hdev
                let jj : J := ⟨j,hj⟩
                have he : s' = Function.update (X x) j (s' j) := by
                  funext k
                  by_cases hk : k=j
                  · simp [hk]
                  · simp [Function.update_of_ne hk, hdev k hk]
                have hres : R s' = Function.update x jj (s' j) := by
                  calc
                    R s' = R (Function.update (X x) j (s' j)) := congrArg R he
                    _ = Function.update x jj (s' j) := by rw [hRU (X x) jj, hxR]
                rw [pR s' hs' jj, pR (X x) hs jj, hxR, hres]
                exact hx.2 jj (s' j) (hR s' hs' jj)
              refine ⟨X x, hseq, ?_⟩
              intro s hsEq
              have hrEq : (∀ j i, R s j i ∈ C j i) ∧
                  ∀ j y, (∀ i, y i ∈ C j i) → F (Function.update (R s) j y) j ≤ F (R s) j := by
                refine ⟨hR s hsEq.1, ?_⟩
                intro j y hy
                have hfu := hfU s hsEq.1 j y hy
                have hh := hsEq.2 j.val j.property (Function.update s j.val y) hfu
                  (fun k hk => Function.update_of_ne hk _ _)
                rwa [pR _ hfu j, pR s hsEq.1 j, hRU] at hh
              have he := huniq (R s) hrEq
              rw [← hXR s hsEq.1, he]
            have concavity (g : Network ι) (j : ι) (s : ι → Firm → ℝ) :
                StrictConcaveOn ℝ {y : Firm → ℝ | ∀ i, ¬ (i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab) → y i = 0}
                  (fun y => tier2Payoff E g (Function.update s j y) j) := by
              let D : Set (Firm → ℝ) := {y | ∀ i, ¬ (i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab) → y i = 0}
              let r (i : Firm) := tier1Qty g s i - if i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab then s j i else 0
              let H (u v : Firm → ℝ) := 2*u .a*v .a+u .a*v .b+u .b*v .a+2*u .b*v .b
              let f (y : Firm → ℝ) := (E.α-E.vT)*(y .a+y .b)-2*E.β*H (r+y) y
              have he (y : Firm → ℝ) (hy : y ∈ D) :
                  tier2Payoff E g (Function.update s j y) j = f y := by
                rw [norm_pay g _ j (by intro i hi; simpa only [Function.update_self] using hy i hi)]
                have hq (i : Firm) : tier1Qty g (Function.update s j y) i = (r+y) i := by
                  rw [qty_up]
                  dsimp [r]
                  by_cases hl : i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab
                  · simp only [if_pos hl]; ring
                  · simp only [if_neg hl, hy i hl, sub_zero, add_zero]
                rw [hq, hq]
                simp only [Function.update_self]
                rfl
              have hc : Convex ℝ D := by
                intro x hx y hy a b ha hb hab i hi
                simp [hx i hi, hy i hi]
              refine ⟨hc, ?_⟩
              intro x hx y hy hxy a b ha hb hab
              change a * tier2Payoff E g (Function.update s j x) j +
                b * tier2Payoff E g (Function.update s j y) j <
                  tier2Payoff E g (Function.update s j (a • x+b • y)) j
              rw [he x hx, he y hy, he _ (hc hx hy ha.le hb.le hab)]
              have hd : 0 < H (x-y) (x-y) := by
                by_contra hn
                have hn' : H (x-y) (x-y) ≤ 0 := le_of_not_gt hn
                dsimp [H] at hn'
                have ha := sq_nonneg (x .a-y .a)
                have hb := sq_nonneg (x .b-y .b)
                have hab := sq_nonneg (x .a-y .a+(x .b-y .b))
                apply hxy
                ext i
                cases i <;> nlinarith
              have hid : f (a • x+b • y)-(a*f x+b*f y) =
                  2*E.β*a*b*H (x-y) (x-y) := by
                have hbe : b=1-a := by linarith
                rw [hbe]
                dsimp [f, H]
                ring
              have hp : 0 < 2*E.β*a*b*H (x-y) (x-y) := by positivity
              linarith
            have pay_two (g : Network ι) (s : ι → Firm → ℝ) (j : ι) :
                tier2Payoff E g s j =
                  (if Firm.a ∈ g.T1 ∧ j ∈ g.excl .a ∪ g.Sab then
                    (E.α-E.vT-4*E.β*tier1Qty g s .a-2*E.β*tier1Qty g s .b)*s j .a else 0) +
                  (if Firm.b ∈ g.T1 ∧ j ∈ g.excl .b ∪ g.Sab then
                    (E.α-E.vT-4*E.β*tier1Qty g s .b-2*E.β*tier1Qty g s .a)*s j .b else 0) := by
              rw [payoff]
              simp_rw [qother]
              have he : g.T1.filter (fun i => j ∈ g.excl i ∪ g.Sab) =
                  Finset.univ.filter (fun i => i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab) := by
                ext i; simp
              rw [he, Finset.sum_filter]
              simp [show (Finset.univ : Finset Firm) = {.a,.b} from rfl, otherFirm]
            have deriv_link (g : Network ι) (s : ι → Firm → ℝ) (j : ι) (i : Firm)
                (hl : i ∈ g.T1 ∧ j ∈ g.excl i ∪ g.Sab) :
                HasDerivAt (fun t => tier2Payoff E g (Function.update s j (Function.update (s j) i t)) j)
                  (-4*E.β*s j i+(E.α-E.vT-4*E.β*tier1Qty g s i-
                    2*E.β*tier1Qty g s (otherFirm i))-
                    2*E.β*(if otherFirm i ∈ g.T1 ∧ j ∈ g.excl (otherFirm i) ∪ g.Sab then s j (otherFirm i) else 0))
                  (s j i) := by
              let u := if otherFirm i ∈ g.T1 ∧ j ∈ g.excl (otherFirm i) ∪ g.Sab then s j (otherFirm i) else 0
              let qa := tier1Qty g s i
              let qb := tier1Qty g s (otherFirm i)
              let z := s j i
              let A := E.α-E.vT
              have hf : (fun t => tier2Payoff E g (Function.update s j (Function.update (s j) i t)) j) =
                  fun t => (A-4*E.β*qb-2*E.β*qa+2*E.β*z)*u +
                    (A-4*E.β*qa+4*E.β*z-2*E.β*qb-2*E.β*u)*t + (-4*E.β)*t^2 := by
                funext t
                rw [pay_two]
                simp only [qty_up, Function.update_self]
                cases i <;> simp only [u, qa, qb, z, A, otherFirm] at hl ⊢
                all_goals
                  simp only [Function.update_self, Function.update_of_ne (show Firm.a ≠ .b by decide),
                    Function.update_of_ne (show Firm.b ≠ .a by decide), sub_self, ite_self, add_zero]
                  split_ifs with hh <;> try contradiction
                  all_goals (try simp only [hh, and_self, ite_true, ite_false]); ring
              rw [hf]
              convert dq ((A-4*E.β*qb-2*E.β*qa+2*E.β*z)*u)
                (A-4*E.β*qa+4*E.β*z-2*E.β*qb-2*E.β*u) (-4*E.β) z using 1 <;>
                dsimp [A, qa, qb, z, u] <;> ring
            refine ⟨fun g _ j _ s => concavity g j s, ?_, ?_⟩
            · exact fun M hM g _ => equilibrium M hM g
            · intro g hg s i hi
              have hqi : tier1Qty g s i = ∑ j ∈ g.excl i ∪ g.Sab, s j i := by
                simp only [tier1Qty, if_pos hi]
              have hqo : (∑ k ∈ g.T1.erase i, ∑ j ∈ g.excl k ∪ g.Sab, s j k) =
                  tier1Qty g s (otherFirm i) := by
                rw [← qother]
                apply Finset.sum_congr rfl
                intro k hk
                simp only [tier1Qty, if_pos (Finset.mem_of_mem_erase hk)]
              rw [← hqi, hqo]
              constructor
              · intro j hj
                have hn : ¬ (otherFirm i ∈ g.T1 ∧ j ∈ g.excl (otherFirm i) ∪ g.Sab) := by
                  intro hh
                  have hm := Finset.mem_union.mp hh.2
                  cases i with
                  | a =>
                    have hj' : j ∈ g.Sa := hj
                    rcases hm with hb | hc
                    · exact Finset.disjoint_left.mp g.hab hj' hb
                    · exact Finset.disjoint_left.mp g.hac hj' hc
                  | b =>
                    have hj' : j ∈ g.Sb := hj
                    rcases hm with ha | hc
                    · exact Finset.disjoint_left.mp g.hab ha hj'
                    · exact Finset.disjoint_left.mp g.hbc hj' hc
                simpa only [if_neg hn, mul_zero, sub_zero] using
                  deriv_link g s j i ⟨hi, Finset.mem_union.mpr (Or.inl hj)⟩
              · intro j hj
                have hT := hg.2.1 ⟨j,hj⟩
                have ho : otherFirm i ∈ g.T1 ∧ j ∈ g.excl (otherFirm i) ∪ g.Sab := by
                  refine ⟨?_, Finset.mem_union.mpr (Or.inr hj)⟩
                  rw [hT]
                  exact Finset.mem_univ _
                have her : g.T1.erase i = {otherFirm i} := by
                  rw [hT]
                  cases i <;> decide
                rw [her, Finset.sum_singleton]
                simpa only [if_pos ho] using
                  deriv_link g s j i ⟨hi, Finset.mem_union.mpr (Or.inr hj)⟩
