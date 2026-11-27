-- Prove2me | solution 1 for SRAudit.TwoPhase.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:24.61382+00:00
-- url     : https://prove2.me/submissions/37a353fe-963e-4dbf-aeca-57fa3d400ca4

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

open SRAudit
open SRAudit.TwoPhase
open SRAudit.TwoPhase.Supplement

open SRAudit.TwoPhase

theorem solution {ι : Type} [DecidableEq ι] (E : Demand) (hE : E.Standing) (M : ℝ) (hM : 0 < M)
    (g : Network ι) (hg : WellFormedNet g) (hnull : ¬ IsNullNet g) :
    ∃! e : ProdOutcome ι, IsProdEq E g M e := by
      set_option maxHeartbeats 0 in
        classical
        have hb : 0 < E.β := hE.1
        have quad (a b x : ℝ) (ha : 0 < a) :
            (∀ y : ℝ, (b - a*y)*y ≤ (b-a*x)*x) ↔ b = 2*a*x := by
          constructor
          · intro h
            have hm : IsLocalMax (fun y : ℝ => (b-a*y)*y) x :=
              (show IsMaxOn (fun y : ℝ => (b-a*y)*y) Set.univ x from fun y _ => h y).isLocalMax (by simp)
            have hd := hm.hasDerivAt_eq_zero
              (((hasDerivAt_const x b).sub ((hasDerivAt_id x).const_mul a)).mul (hasDerivAt_id x))
            dsimp at hd
            linarith
          · intro h y
            rw [h]
            nlinarith [mul_nonneg ha.le (sq_nonneg (y-x))]
        have buyer (p q : ℝ) : IsBuyerOptimal E p q ↔ p = E.α-E.v0-2*E.β*q := by
          have heq (y : ℝ) : buyerProfit E p y = (E.α-E.v0-p-E.β*y)*y := by
            unfold buyerProfit
            ring
          simp only [IsBuyerOptimal, heq]
          rw [quad E.β (E.α-E.v0-p) q hb]
          constructor <;> intro h <;> linarith
        have inv1 (q : ℝ) : invDemand1 E q = E.α-E.v0-2*E.β*q := by
          have hx : ∃! p : ℝ, IsBuyerOptimal E p q := by
            refine ⟨E.α-E.v0-2*E.β*q, (buyer _ _).2 rfl, ?_⟩
            intro p hp
            exact (buyer p q).1 hp
          simp only [invDemand1, dif_pos hx]
          exact (buyer _ _).1 hx.exists.choose_spec
        have sumupd (q : Firm → ℝ) (i : Firm) (hi : i ∈ g.T1) (y : ℝ) :
            (∑ k ∈ g.T1, Function.update q i y k) = (∑ k ∈ g.T1, q k) - q i + y := by
          rw [Finset.sum_update_of_mem hi]
          have he := Finset.sum_erase_add g.T1 q hi
          simpa only [Finset.sdiff_singleton_eq_erase] using
            (show y + ∑ k ∈ g.T1.erase i, q k = (∑ k ∈ g.T1, q k) - q i + y by linarith)
        have tier1 (p q : Firm → ℝ) : IsTier1Eq E g p q ↔
            (∀ x, x ∉ g.T1 → q x = 0) ∧
            ∀ i ∈ g.T1, p i = E.α-E.v0-E.v1-2*E.β*((∑ k ∈ g.T1, q k)+q i) := by
          constructor
          · rintro ⟨hn, ho⟩
            refine ⟨hn, ?_⟩
            intro i hi
            have h := ho i hi
            simp only [tier1Payoff, inv1, sumupd q i hi, Function.update_self] at h
            have h' : ∀ y : ℝ,
                ((E.α-E.v0-E.v1-p i-2*E.β*((∑ k ∈ g.T1, q k)-q i))-(2*E.β)*y)*y ≤
                ((E.α-E.v0-E.v1-p i-2*E.β*((∑ k ∈ g.T1, q k)-q i))-(2*E.β)*q i)*q i := by
              intro y
              convert h y using 1 <;> ring
            have hf := (quad (2*E.β) _ (q i) (by positivity)).1 h'
            linarith
          · rintro ⟨hn, hf⟩
            refine ⟨hn, ?_⟩
            intro i hi y
            have h := (quad (2*E.β)
              (E.α-E.v0-E.v1-p i-2*E.β*((∑ k ∈ g.T1, q k)-q i)) (q i) (by positivity)).2
              (by have := hf i hi; linarith) y
            simp only [tier1Payoff, inv1, sumupd q i hi, Function.update_self]
            convert h using 1 <;> ring
        have inv2 (q : Firm → ℝ) (hq : ∀ i, i ∉ g.T1 → q i = 0) :
            invDemand2 E g q = fun i => if i ∈ g.T1 then
              E.α-E.v0-E.v1-2*E.β*((∑ k ∈ g.T1, q k)+q i) else 0 := by
          let p : Firm → ℝ := fun i => if i ∈ g.T1 then
            E.α-E.v0-E.v1-2*E.β*((∑ k ∈ g.T1, q k)+q i) else 0
          have hx : ∃! p : Firm → ℝ, (∀ i, i ∉ g.T1 → p i = 0) ∧ IsTier1Eq E g p q := by
            refine ⟨p, ⟨?_, (tier1 p q).2 ⟨hq, ?_⟩⟩, ?_⟩
            · intro i hi
              simp [p, hi]
            · intro i hi
              simp [p, hi]
            · intro p' hp
              funext i
              by_cases hi : i ∈ g.T1
              · simpa [p, hi] using (tier1 p' q).1 hp.2 |>.2 i hi
              · simp [hp.1 i hi, p, hi]
          change (if h : ∃! p2 : Firm → ℝ, _ then _ else _) = p
          rw [dif_pos hx]
          apply hx.unique hx.exists.choose_spec
          exact ⟨(by intro i hi; simp [p, hi]),
            (tier1 p q).2 ⟨hq, by intro i hi; simp [p, hi]⟩⟩
        let J := {j // j ∈ g.S2}
        let X := J → Firm → ℝ
        let Q : X → Firm → ℝ := fun x i => ∑ j, x j i
        let R : X → J → ℝ := fun x j => ∑ i, x j i
        let T : X → ℝ := fun x => ∑ j, R x j
        let B : X → X → ℝ := fun x y =>
          T x * T y + (∑ i, Q x i * Q y i) +
            (∑ j, R x j * R y j) + ∑ j, ∑ i, x j i * y j i
        have Qadd (x y : X) : Q (x+y) = Q x + Q y := by
          funext i
          simp [Q, X, Pi.add_apply, Finset.sum_add_distrib]
        have Radd (x y : X) : R (x+y) = R x + R y := by
          funext j
          simp [R, X, Pi.add_apply, Finset.sum_add_distrib]
        have Tadd (x y : X) : T (x+y) = T x + T y := by
          simp [T, Radd, Finset.sum_add_distrib]
        have Qsmul (t : ℝ) (x : X) : Q (t • x) = t • Q x := by
          funext i
          simp [Q, X, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        have Rsmul (t : ℝ) (x : X) : R (t • x) = t • R x := by
          funext j
          simp [R, X, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        have Tsmul (t : ℝ) (x : X) : T (t • x) = t * T x := by
          simp [T, Rsmul, Finset.mul_sum]
        have Bsym (x y : X) : B x y = B y x := by
          dsimp [B]
          simp only [mul_comm]
        have Badd (x y z : X) : B x (y+z) = B x y + B x z := by
          dsimp [B]
          rw [Tadd, Qadd, Radd]
          simp only [X, Pi.add_apply, mul_add, Finset.sum_add_distrib]
          ring
        have Bsmul (x y : X) (t : ℝ) : B x (t • y) = t * B x y := by
          dsimp [B]
          rw [Tsmul, Qsmul, Rsmul]
          simp only [X, Pi.smul_apply, smul_eq_mul]
          simp only [mul_assoc, mul_left_comm _ t, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
        have Bnonneg (x : X) : 0 ≤ B x x := by
          dsimp [B]
          exact add_nonneg (add_nonneg (add_nonneg (mul_self_nonneg _)
            (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)))
            (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)))
            (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)))
        have Bzero (x : X) (hx : B x x = 0) : x = 0 := by
          have hh : (∑ j, ∑ i, x j i * x j i) ≤ B x x := by
            dsimp [B]
            have h1 : 0 ≤ T x * T x := mul_self_nonneg _
            have h2 : 0 ≤ ∑ i, Q x i * Q x i := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
            have h3 : 0 ≤ ∑ j, R x j * R x j := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
            linarith
          have hs : ∀ j : J, (∑ i, x j i * x j i) = 0 := by
            intro j
            apply (Finset.sum_eq_zero_iff_of_nonneg
              (fun j _ => Finset.sum_nonneg (fun _ _ => mul_self_nonneg _))).1
            · exact le_antisymm (by linarith)
                (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)))
            · exact Finset.mem_univ j
          funext j i
          have hi := (Finset.sum_eq_zero_iff_of_nonneg
            (fun i _ => mul_self_nonneg (x j i))).1 (hs j) i (Finset.mem_univ i)
          exact mul_self_eq_zero.mp hi
        let C := E.α-E.v0-E.v1-E.v2
        let F : X → ℝ := fun x => C*T x-E.β*B x x
        let L : X → X → ℝ := fun x d => C*T d-2*E.β*B x d
        have expand (x d : X) (t : ℝ) :
            F (x+t • d)-F x = t*L x d-t^2*E.β*B d d := by
          dsimp [F, L]
          rw [Tadd, Tsmul, Badd, Bsmul, Bsym (x+t • d) x,
            Badd, Bsmul, Bsym (x+t • d) d, Badd, Bsmul, Bsym d x]
          ring
        let link : J → Firm → Prop := fun j i => i ∈ g.T1 ∧ j.val ∈ g.excl i ∪ g.Sab
        let K : Set X := {x | ∀ j i, 0 ≤ x j i ∧ x j i ≤ M ∧ (¬ link j i → x j i = 0)}
        have Kzero : (0 : X) ∈ K := by
          intro j i
          exact ⟨le_rfl, hM.le, fun _ => rfl⟩
        have Kcompact : IsCompact K := by
          have hc : IsClosed K := by
            change IsClosed {x : X | ∀ j i, 0 ≤ x j i ∧ x j i ≤ M ∧ (¬ link j i → x j i = 0)}
            simp only [Set.setOf_forall]
            apply isClosed_iInter
            intro j
            apply isClosed_iInter
            intro i
            apply IsClosed.inter
            · exact isClosed_le continuous_const (show Continuous (fun x : X => x j i) by fun_prop)
            apply IsClosed.inter
            · exact isClosed_le (show Continuous (fun x : X => x j i) by fun_prop) continuous_const
            change IsClosed {x : X | ¬ link j i → x j i = 0}
            by_cases h : link j i
            · have heq : {x : X | ¬ link j i → x j i = 0} = Set.univ := by
                ext x
                simp [h]
              rw [heq]
              exact isClosed_univ
            · simp only [h, not_false_eq_true, true_implies]
              exact isClosed_eq (show Continuous (fun x : X => x j i) by fun_prop) continuous_const
          apply (isCompact_Icc (a := (0 : X)) (b := fun _ _ => M)).of_isClosed_subset hc
          intro x hx
          exact ⟨fun j i => (hx j i).1, fun j i => (hx j i).2.1⟩
        have Kseg (x y : X) (hx : x ∈ K) (hy : y ∈ K) (t : ℝ)
            (ht : t ∈ Set.Icc (0 : ℝ) 1) : x + t • (y-x) ∈ K := by
          intro j i
          have h1 := hx j i
          have h2 := hy j i
          change 0 ≤ x j i+t*(y j i-x j i) ∧
            x j i+t*(y j i-x j i) ≤ M ∧
            (¬ link j i → x j i+t*(y j i-x j i)=0)
          refine ⟨?_, ?_, ?_⟩
          · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) h1.1, mul_nonneg ht.1 h2.1]
          · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h1.2.1),
              mul_nonneg ht.1 (sub_nonneg.mpr h2.2.1)]
          · intro h
            rw [h1.2.2 h, h2.2.2 h]
            ring
        have Fcont : Continuous F := by
          dsimp [F, B, T, R, Q]
          fun_prop
        obtain ⟨xstar, hxstar, hmax⟩ := Kcompact.exists_isMaxOn ⟨0, Kzero⟩ Fcont.continuousOn
        let S : X → ι → Firm → ℝ := fun x j i => if h : j ∈ g.S2 then x ⟨j,h⟩ i else 0
        let res : (ι → Firm → ℝ) → X := fun s j i => s j.val i
        have linkS2 (j : ι) (i : Firm) (h : j ∈ g.excl i ∪ g.Sab) : j ∈ g.S2 := by
          cases i
          · exact Finset.mem_union.mpr (Or.elim (Finset.mem_union.mp h)
              (fun ha => Or.inl (Finset.mem_union.mpr (Or.inl ha))) Or.inr)
          · exact Finset.mem_union.mpr (Or.elim (Finset.mem_union.mp h)
              (fun hb => Or.inl (Finset.mem_union.mpr (Or.inr hb))) Or.inr)
        have Sres (s : ι → Firm → ℝ) (hs : Feasible2 g M s) : S (res s) = s := by
          funext j i
          dsimp [S, res]
          split_ifs with hj
          · rfl
          · symm
            exact (hs j i).2 (fun h => hj (linkS2 j i h.2))
        have resS (x : X) : res (S x) = x := by
          funext j i
          simp [res, S, j.property]
        have feasS (x : X) (hx : x ∈ K) : Feasible2 g M (S x) := by
          intro j i
          by_cases hj : j ∈ g.S2
          · simp only [S, dif_pos hj]
            exact ⟨fun _ => ⟨(hx ⟨j,hj⟩ i).1, (hx ⟨j,hj⟩ i).2.1⟩, (hx ⟨j,hj⟩ i).2.2⟩
          · simp only [S, dif_neg hj]
            exact ⟨fun _ => ⟨le_rfl, hM.le⟩, by simp⟩
        have feasres (s : ι → Firm → ℝ) (hs : Feasible2 g M s) : res s ∈ K := by
          intro j i
          by_cases h : link j i
          · exact ⟨(hs j.val i).1 h |>.1, (hs j.val i).1 h |>.2,
              fun hh => (hh h).elim⟩
          · have he := (hs j.val i).2 h
            exact ⟨by simpa [res, he], by simpa [res, he] using hM.le,
              he ▸ fun _ => rfl⟩
        have qtyS (x : X) (hx : x ∈ K) : tier1Qty g (S x) = Q x := by
          funext i
          have hz (j : J) (hj : j.val ∉ g.excl i ∪ g.Sab) : x j i = 0 :=
            (hx j i).2.2 (fun h => hj h.2)
          by_cases hi : i ∈ g.T1
          · simp only [tier1Qty, if_pos hi]
            rw [show (∑ j ∈ g.excl i ∪ g.Sab, S x j i) = ∑ j ∈ g.S2, S x j i from
              Finset.sum_subset (fun j hj => linkS2 j i hj) (fun j hj hji => by
                dsimp [S]
                rw [dif_pos hj]
                exact hz ⟨j,hj⟩ hji)]
            change (∑ j ∈ g.S2, S x j i) = ∑ j : J, x j i
            rw [← Finset.sum_attach]
            apply Finset.sum_congr rfl
            intro j hj
            simp [S, j.property]
          · simp only [tier1Qty, if_neg hi]
            symm
            exact Finset.sum_eq_zero (fun j _ => (hx j i).2.2 (fun h => hi h.1))
        have Qoff (x : X) (hx : x ∈ K) (i : Firm) (hi : i ∉ g.T1) : Q x i = 0 := by
          exact Finset.sum_eq_zero (fun j _ => (hx j i).2.2 (fun h => hi h.1))
        have sumQ (x : X) (hx : x ∈ K) : (∑ i ∈ g.T1, Q x i) = T x := by
          calc
            (∑ i ∈ g.T1, Q x i) = ∑ i, Q x i := by
              apply Finset.sum_subset (Finset.subset_univ _)
              intro i _ hi
              exact Qoff x hx i hi
            _ = T x := by
              dsimp [Q, T, R]
              rw [Finset.sum_comm]
        have sumFirm (f : Firm → ℝ) : (∑ i, f i) = f .a + f .b := by
          change f .a + (f .b + 0) = _
          ring
        let P : X → J → ℝ := fun x j =>
          C * R x j - 2*E.β*(T x * R x j + ∑ i, Q x i * x j i)
        have payoff (x : X) (hx : x ∈ K) (j : J) : tier2Payoff E g (S x) j.val = P x j := by
          rw [tier2Payoff, qtyS x hx, inv2 (Q x) (Qoff x hx)]
          have he : (∑ i ∈ g.T1.filter (fun i => j.val ∈ g.excl i ∪ g.Sab),
              ((if i ∈ g.T1 then E.α-E.v0-E.v1-2*E.β*((∑ k ∈ g.T1, Q x k)+Q x i) else 0)-E.v2)*S x j.val i) =
              ∑ i, (C-2*E.β*(T x+Q x i))*x j i := by
            rw [sumQ x hx]
            calc
              _ = ∑ i ∈ g.T1.filter (fun i => j.val ∈ g.excl i ∪ g.Sab),
                    (C-2*E.β*(T x+Q x i))*x j i := by
                apply Finset.sum_congr rfl
                intro i hi
                have hi' := Finset.mem_filter.mp hi
                simp only [if_pos hi'.1, S, dif_pos j.property]
                dsimp [C]
                ring
              _ = _ := by
                apply Finset.sum_subset (Finset.subset_univ _)
                intro i _ hi
                have hz : x j i = 0 := (hx j i).2.2
                  (by simpa [link, Finset.mem_filter] using hi)
                rw [hz, mul_zero]
          rw [he]
          dsimp [P, R]
          simp only [sumFirm]
          ring
        let U : J → (Firm → ℝ) → X := fun j r k i => if k = j then r i else 0
        have QU (j : J) (r : Firm → ℝ) : Q (U j r) = r := by
          funext i
          dsimp [Q, U]
          rw [Finset.sum_eq_single j]
          · simp
          · intro k hk hkj
            simp [hkj]
          · simp
        have RU (j k : J) (r : Firm → ℝ) : R (U j r) k = if k=j then ∑ i, r i else 0 := by
          dsimp [R, U]
          split_ifs <;> simp
        have TU (j : J) (r : Firm → ℝ) : T (U j r) = ∑ i, r i := by
          dsimp [T]
          rw [Finset.sum_eq_single j]
          · simp [RU]
          · intro k hk hkj
            simp [RU, hkj]
          · simp
        have BU (x : X) (j : J) (r : Firm → ℝ) :
            B x (U j r) = T x*(∑ i, r i)+(∑ i, Q x i*r i)+
              R x j*(∑ i, r i)+∑ i, x j i*r i := by
          have hsr : (∑ k, R x k * R (U j r) k) = R x j * (∑ i, r i) := by
            rw [Finset.sum_eq_single j]
            · simp [RU]
            · intro k hk hkj
              simp [RU, hkj]
            · simp
          have hsx : (∑ k, ∑ i, x k i * U j r k i) = ∑ i, x j i * r i := by
            rw [Finset.sum_eq_single j]
            · simp [U]
            · intro k hk hkj
              simp [U, hkj]
            · simp
          dsimp only [B]
          rw [TU, QU, hsr, hsx]
        have PU (x : X) (j : J) (r : Firm → ℝ) (t : ℝ) :
            P (x+t • U j r) j - P x j = F (x+t • U j r)-F x := by
          have row (i : Firm) : (x+t • U j r) j i = x j i+t*r i := by
            change x j i+t*(if j=j then r i else 0) = _
            rw [if_pos rfl]
          rw [expand]
          dsimp only [P, L]
          simp only [Tadd, Tsmul, TU, Radd, Rsmul, RU, Qadd, Qsmul, QU,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_pos rfl, row]
          simp only [BU, TU, QU, RU, if_pos rfl, ite_true]
          simp only [X, sumFirm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, U, if_pos rfl, ite_true]
          ring
        have Krow (x y : X) (hx : x ∈ K) (hy : y ∈ K) (j : J)
            (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
            x + t • U j (y j - x j) ∈ K := by
          intro k i
          by_cases hk : k = j
          · subst k
            simpa only [X, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, U, if_pos rfl, ite_true]
              using Kseg x y hx hy t ht j i
          · simpa only [X, Pi.add_apply, Pi.smul_apply, smul_eq_mul, U, if_neg hk, mul_zero, add_zero]
              using hx k i
        have fixrow (x : X) (j : J) (r : Firm → ℝ) (t : ℝ) :
            ∀ k : ι, k ≠ j.val → S (x + t • U j r) k = S x k := by
          intro k hk
          funext i
          dsimp [S]
          split_ifs with hk2
          · have hn : (⟨k, hk2⟩ : J) ≠ j := by
              intro hh
              exact hk (congrArg Subtype.val hh)
            simp only [X, Pi.add_apply, Pi.smul_apply, smul_eq_mul, U, if_neg hn, mul_zero, add_zero]
          · rfl
        have eqstar : IsTier2Eq E g M (S xstar) := by
          refine ⟨feasS xstar hxstar, ?_⟩
          intro j hj s' hs' hfix
          let jj : J := ⟨j, hj⟩
          let y : X := res s'
          have hy : y ∈ K := feasres s' hs'
          have he : y = xstar + (1 : ℝ) • U jj (y jj - xstar jj) := by
            funext k i
            by_cases hk : k = jj
            · subst k
              simp only [X, one_smul, Pi.add_apply, Pi.sub_apply, U, if_pos rfl, ite_true]
              ring
            · have hkj : k.val ≠ j := by
                intro h
                exact hk (Subtype.ext h)
              have hf := congrFun (hfix k.val hkj) i
              change s' k.val i = _
              simpa [X, S, k.property, U, hk] using hf
          have hd := PU xstar jj (y jj - xstar jj) 1
          rw [← he] at hd
          have hm : F y ≤ F xstar := hmax hy
          have hpy : tier2Payoff E g s' j = P y jj := by
            have hp := payoff y hy jj
            rw [show S y = s' from Sres s' hs'] at hp
            exact hp
          have hpx : tier2Payoff E g (S xstar) j = P xstar jj := payoff xstar hxstar jj
          linarith
        have slope (a b : ℝ) (hb0 : 0 ≤ b)
            (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, t*a-t^2*b ≤ 0) : a ≤ 0 := by
          by_contra hn
          have ha : 0 < a := lt_of_not_ge hn
          let t : ℝ := min 1 (a / (2*(b+1)))
          have ht : 0 < t := lt_min (by norm_num) (div_pos ha (by positivity))
          have ht1 : t ≤ 1 := min_le_left _ _
          have htb : t ≤ a / (2*(b+1)) := min_le_right _ _
          have hta : t*(2*(b+1)) ≤ a := (le_div_iff₀ (by positivity)).mp htb
          have hsmall : t*b < a := by nlinarith [mul_nonneg ht.le hb0]
          have hh := h t ⟨ht.le, ht1⟩
          have hp := mul_pos ht (sub_pos.mpr hsmall)
          nlinarith
        have Ladd (x d e : X) : L x (d+e) = L x d + L x e := by
          dsimp [L]
          rw [Tadd, Badd]
          ring
        have Lzero (x : X) : L x 0 = 0 := by
          simp [X, L, B, T, R, Q]
        have sumU (d : X) : (∑ j, U j (d j)) = d := by
          funext k i
          simp only [X, Finset.sum_apply, U]
          rw [Finset.sum_eq_single k]
          · simp
          · intro j hj hjk
            simp [Ne.symm hjk]
          · simp
        have Lsum (x d : X) : L x d = ∑ j, L x (U j (d j)) := by
          let l : X →+ ℝ := { toFun := L x, map_zero' := Lzero x, map_add' := Ladd x }
          have hh : L x (∑ j, U j (d j)) = ∑ j, L x (U j (d j)) := by
            change l (∑ j, U j (d j)) = ∑ j, l (U j (d j))
            exact map_sum l _ _
          rw [sumU] at hh
          exact hh
        have VI (x : X) (hx : x ∈ K) (heq : IsTier2Eq E g M (S x)) :
            ∀ y ∈ K, L x (y-x) ≤ 0 := by
          intro y hy
          rw [Lsum]
          apply Finset.sum_nonpos
          intro j hj
          apply slope _ (E.β * B (U j ((y-x) j)) (U j ((y-x) j)))
            (mul_nonneg hb.le (Bnonneg _))
          intro t ht
          let z : X := x+t • U j (y j - x j)
          have hz : z ∈ K := Krow x y hx hy j t ht
          have hn := heq.2 j.val j.property (S z) (feasS z hz)
            (fixrow x j (y j-x j) t)
          rw [payoff z hz j, payoff x hx j] at hn
          have hd := PU x j (y j-x j) t
          have hf := expand x (U j (y j-x j)) t
          change t * L x (U j (y j - x j)) -
            t ^ 2 * (E.β * B (U j (y j - x j)) (U j (y j - x j))) ≤ 0
          dsimp [z] at hn
          nlinarith
        have eqmax (x : X) (hx : x ∈ K) (heq : IsTier2Eq E g M (S x)) :
            IsMaxOn F K x := by
          intro y hy
          change F y ≤ F x
          have hv := VI x hx heq y hy
          have he := expand x (y-x) 1
          have hab : x + (y-x) = y := by abel
          rw [one_smul, hab] at he
          norm_num only [one_mul, one_pow, pow_one] at he
          have hp := mul_nonneg hb.le (Bnonneg (y-x))
          linarith
        have unique2 (s : ι → Firm → ℝ) (hs : IsTier2Eq E g M s) : s = S xstar := by
          let x : X := res s
          have hx : x ∈ K := feasres s hs.1
          have hS : S x = s := Sres s hs.1
          have heq : IsTier2Eq E g M (S x) := hS.symm ▸ hs
          have hv := VI x hx heq xstar hxstar
          have hm : F xstar ≤ F x := eqmax x hx heq hxstar
          have hm' : F x ≤ F xstar := hmax hx
          have he := expand x (xstar-x) 1
          have hab : x + (xstar-x) = xstar := by abel
          rw [one_smul, hab] at he
          norm_num only [one_mul, one_pow, pow_one] at he
          have hB : B (xstar-x) (xstar-x) = 0 := by
            have hn := Bnonneg (xstar-x)
            apply le_antisymm _ hn
            by_contra hh
            have hp := mul_pos hb (lt_of_not_ge hh)
            linarith
          have hd := Bzero (xstar-x) hB
          have hexx : x = xstar := (sub_eq_zero.mp hd).symm
          rw [← hS, hexx]
        have unique1 (p q r : Firm → ℝ) (hq : IsTier1Eq E g p q)
            (hr : IsTier1Eq E g p r) : q = r := by
          have hq' := (tier1 p q).1 hq
          have hr' := (tier1 p r).1 hr
          have he (i : Firm) (hi : i ∈ g.T1) :
              (∑ k ∈ g.T1, q k)+q i = (∑ k ∈ g.T1, r k)+r i := by
            apply mul_left_cancel₀ (show (2*E.β) ≠ 0 by positivity)
            have h1 := hq'.2 i hi
            have h2 := hr'.2 i hi
            linarith
          have hs : (∑ k ∈ g.T1, q k) = (∑ k ∈ g.T1, r k) := by
            rcases le_total (∑ k ∈ g.T1, q k) (∑ k ∈ g.T1, r k) with h | h
            · apply le_antisymm h
              apply Finset.sum_le_sum
              intro i hi
              have hh := he i hi
              linarith
            · apply le_antisymm _ h
              apply Finset.sum_le_sum
              intro i hi
              have hh := he i hi
              linarith
          funext i
          by_cases hi : i ∈ g.T1
          · have hh := he i hi
            linarith
          · rw [hq'.1 i hi, hr'.1 i hi]
        let q : Firm → ℝ := Q xstar
        let p : Firm → ℝ := invDemand2 E g q
        let qc : ℝ := ∑ i ∈ g.T1, q i
        let p1 : ℝ := invDemand1 E qc
        have hq : IsTier1Eq E g p q := by
          apply (tier1 p q).2
          refine ⟨Qoff xstar hxstar, ?_⟩
          intro i hi
          dsimp [p, q]
          rw [inv2 (Q xstar) (Qoff xstar hxstar)]
          simp only [if_pos hi]
        let e : ProdOutcome ι := ⟨E.α-E.β*qc, p1, p, qc, q, S xstar⟩
        have he : IsProdEq E g M e := by
          refine ⟨eqstar, ?_, hq, rfl, ?_, rfl⟩
          · change p = invDemand2 E g (tier1Qty g (S xstar))
            rw [qtyS xstar hxstar]
          · apply (buyer p1 qc).2
            exact inv1 qc
        refine ⟨e, he, ?_⟩
        intro e' he'
        have hs : e'.s2 = S xstar := unique2 e'.s2 he'.1
        have hp : e'.p2 = p := by
          rw [he'.2.1, hs, qtyS xstar hxstar]
        have hq' : e'.q1 = q := unique1 p e'.q1 q (hp ▸ he'.2.2.1) hq
        have hp1 : e'.p1 = p1 := by
          rw [he'.2.2.2.1, hq']
        have hqc : e'.qc = qc := by
          have hbo := (buyer e'.p1 e'.qc).1 he'.2.2.2.2.1
          have hbo' := inv1 qc
          change p1 = E.α-E.v0-2*E.β*qc at hbo'
          rw [hp1] at hbo
          apply mul_left_cancel₀ (show (2*E.β) ≠ 0 by positivity)
          linarith
        have hp0 : e'.p0 = E.α-E.β*qc := by
          rw [he'.2.2.2.2.2, hqc]
        cases e'
        change ProdOutcome.mk _ _ _ _ _ _ =
          ProdOutcome.mk (E.α-E.β*qc) p1 p qc q (S xstar)
        simp only [ProdOutcome.mk.injEq]
        exact ⟨hp0, hp1, hp, hqc, hq', hs⟩
