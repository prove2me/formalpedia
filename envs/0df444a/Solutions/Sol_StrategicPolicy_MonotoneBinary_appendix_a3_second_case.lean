-- Prove2me | solution 1 for StrategicPolicy.MonotoneBinary.appendix_a3_second_case
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T11:35:18.666409+00:00
-- url     : https://prove2.me/submissions/3d9139b4-0962-41ca-85a9-18a8832e9b3f

import Definitions.Def_StrategicPolicy_MonotoneBinary_Setting
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace BinaryResearch
open StrategicPolicy.MonotoneBinary
variable {m : ℕ} [NeZero m]
lemma br_spec (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ) (i : Fin m) :
    (∀ j,π j-c i j≤π (br c q π i)-c i (br c q π i)) ∧
    (∀ j,(∀ l,π l-c i l≤π j-c i j) → q j≤q (br c q π i)) := by
  have hb : br c q π i∈bestOutcome c q π i := by unfold br;exact Finset.min'_mem _ _
  have h := Finset.mem_filter.mp hb
  have hm := (Finset.mem_filter.mp h.1).2
  exact ⟨hm,fun j hj => h.2 j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)⟩
lemma cost_nonneg (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hs : Standing p q γ c) (hc : OMCost q c) (i j : Fin m) : 0≤c i j := by
  by_cases he : i=j
  · subst j;rw [hs.cost_self]
  · by_cases hq : q i≤q j
    · exact (hs.positive_improvement i j he hq).le
    · rw [(hc.2 i j he).mp (lt_of_not_ge hq)]
lemma cost_mono (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hs : Standing p q γ c) (hc : OMCost q c) (k i j : Fin m)
    (hq : q i≤q j) : c k i≤c k j := by
  by_cases hij : i=j
  · subst j;exact le_rfl
  have hqij : q i<q j := lt_of_le_of_ne hq (fun h => hij (hs.outcome_order.injective h))
  by_cases hki : k=i
  · subst i;rw [hs.cost_self];exact cost_nonneg p q γ c hs hc k j
  by_cases hqi : q i<q k
  · rw [(hc.2 k i hki).mp hqi];exact cost_nonneg p q γ c hs hc k j
  have hqki : q k<q i := lt_of_le_of_ne (le_of_not_gt hqi) (fun h => hki (hs.outcome_order.injective h))
  have hkj : k≠j := fun h => by rw [h] at hqki;linarith
  exact ((hc.1 k i j hki hij hkj).mp ⟨hqki,hqij⟩).1.le
lemma nonworsening (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hs : Standing p q γ c) (hc : OMCost q c) (π : Fin m → ℝ)
    (hmono : OMPolicy q π) (i : Fin m) : q i≤q (br c q π i) := by
  let j := br c q π i
  have hb := br_spec c q π i
  by_contra hn
  have hq : q j<q i := lt_of_not_ge hn
  have hij : i≠j := fun h => by rw [h] at hq;exact lt_irrefl _ hq
  have hzero : c i j=0 := (hc.2 i j hij).mp hq
  have hpi : π j≤π i := by
    by_contra h
    have := hmono i j (lt_of_not_ge h)
    linarith
  have hbest : ∀ l,π l-c i l≤π i-c i i := by
    intro l
    have h := hb.1 l
    change π l-c i l≤π j-c i j at h
    rw [hzero] at h
    rw [hs.cost_self]
    linarith
  exact (not_le_of_gt hq) (hb.2 i hbest)

noncomputable def upper (π : Fin m → ℝ) (i : Fin m) : ℝ :=
  (Finset.Ici i).sup' ⟨i,Finset.mem_Ici.mpr le_rfl⟩ π
lemma upper_self (π : Fin m → ℝ) (i : Fin m) : π i≤upper π i :=
  Finset.le_sup' π (Finset.mem_Ici.mpr le_rfl)
lemma upper_witness (π : Fin m → ℝ) (i : Fin m) : ∃ j,i≤j ∧ upper π i=π j := by
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup' ⟨i,Finset.mem_Ici.mpr le_rfl⟩ π
  exact ⟨j,Finset.mem_Ici.mp hj,he⟩
lemma upper_anti (π : Fin m → ℝ) : Antitone (upper π) := by
  intro i j hij
  obtain ⟨k,hjk,hk⟩ := upper_witness π j
  rw [hk]
  exact Finset.le_sup' π (Finset.mem_Ici.mpr (hij.trans hjk))
noncomputable def envelope (q π : Fin m → ℝ) (γ : ℝ) (i : Fin m) : ℝ :=
  if γ<q i then upper π i else 0
lemma envelope_policy (q π : Fin m → ℝ) (γ : ℝ) (hπ : π∈Policies m) :
    envelope q π γ∈Policies m := by
  intro i
  by_cases h : γ<q i
  · obtain ⟨j,hij,hj⟩ := upper_witness π i
    simpa [envelope,h,hj] using hπ j
  · simp [envelope,h]
lemma envelope_mono (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hs : Standing p q γ c) (π : Fin m → ℝ) (hπ : π∈Policies m) :
    OMPolicy q (envelope q π γ) := by
  intro i j hij
  by_contra h
  have hq : q j≤q i := le_of_not_gt h
  have hπ' := envelope_policy q π γ hπ
  have hgj : γ<q j := by
    by_contra hg
    have hj0 : envelope q π γ j=0 := by simp [envelope,hg]
    rw [hj0] at hij
    exact not_lt_of_ge (hπ' i).1 hij
  have hgi : γ<q i := hgj.trans_le hq
  have hidx : i≤j := by
    by_contra hn
    have := hs.outcome_order (lt_of_not_ge hn)
    linarith
  have ha := upper_anti π hidx
  simp only [envelope,if_pos hgi,if_pos hgj] at hij
  linarith
end BinaryResearch
namespace BinaryResearch
open StrategicPolicy.MonotoneBinary
variable {m : ℕ} [NeZero m]
lemma envelope_improves (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hs : Standing p q γ c) (hc : OMCost q c) (π : Fin m → ℝ) (hπ : π∈Policies m) :
    u p q γ c π≤u p q γ c (envelope q π γ) := by
  let π' := envelope q π γ
  have hπ' : π'∈Policies m := envelope_policy q π γ hπ
  have payoff (i : Fin m) :
      (q (br c q π i)-γ)*π (br c q π i) ≤ (q (br c q π' i)-γ)*π' (br c q π' i) := by
    let j := br c q π i
    let k := br c q π' i
    have ho := br_spec c q π i
    have hn := br_spec c q π' i
    have hright : 0≤(q k-γ)*π' k := by
      by_cases hg : γ<q k
      · exact mul_nonneg (sub_nonneg.mpr hg.le) (hπ' k).1
      · simp [π',envelope,hg]
    by_cases hgj : γ<q j
    swap
    · exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hgj)) (hπ j).1).trans hright
    have hpi : π j≤π' j := by simpa [π',envelope,hgj] using upper_self π j
    have hzero : 0≤π j-c i j := by
      have h := ho.1 i
      change π i-c i i≤π j-c i j at h
      rw [hs.cost_self] at h
      linarith [(hπ i).1]
    have hbound (l : Fin m) : π' l-c i l≤π j-c i j := by
      by_cases hgl : γ<q l
      · obtain ⟨z,hlz,hz⟩ := upper_witness π l
        have hcost := cost_mono p q γ c hs hc i z l (hs.outcome_order.antitone hlz)
        have harg := ho.1 z
        change π z-c i z≤π j-c i j at harg
        dsimp [π']
        rw [envelope,if_pos hgl,hz]
        linarith
      · have hcost := cost_nonneg p q γ c hs hc i l
        simp only [π',envelope,if_neg hgl]
        linarith
    have hbestj : ∀ l,π' l-c i l≤π' j-c i j := by
      intro l
      exact (hbound l).trans (sub_le_sub_right hpi _)
    have hqjk : q j≤q k := hn.2 j hbestj
    have hcost := cost_mono p q γ c hs hc i j k hqjk
    have hprob : π j≤π' k := by
      have hn' := hn.1 j
      change π' j-c i j≤π' k-c i k at hn'
      linarith
    exact mul_le_mul (sub_le_sub_right hqjk γ) hprob (hπ j).1
      (sub_nonneg.mpr (hgj.le.trans hqjk))
  unfold u
  apply Finset.sum_le_sum
  intro i hi
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (payoff i) (hs.p_nonneg i)
lemma monotone_optimum (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hs : Standing p q γ c) (hc : OMCost q c) (πstar : Fin m → ℝ)
    (hopt : Optimal p q γ c πstar) :
    ∃ π∈Policies m,OMPolicy q π ∧ u p q γ c π=u p q γ c πstar := by
  have hm := envelope_policy q πstar γ hopt.1
  refine ⟨envelope q πstar γ,hm,envelope_mono p q γ c hs πstar hopt.1,?_⟩
  exact le_antisymm (hopt.2 hm) (envelope_improves p q γ c hs hc πstar hopt.1)
end BinaryResearch
namespace BinaryResearch
open StrategicPolicy.MonotoneBinary
variable {m : ℕ} [NeZero m]
lemma policy_anti (q π : Fin m → ℝ) (hq : StrictAnti q) (hm : OMPolicy q π) : Antitone π := by
  intro i j hij
  by_contra h
  have := hm i j (lt_of_not_ge h)
  have := hq.antitone hij
  linarith
lemma mono_of_anti (q π : Fin m → ℝ) (hq : StrictAnti q) (hπ : Antitone π) : OMPolicy q π := by
  intro i j hij
  have hji : j <  i := by
    by_contra h
    have := hπ (le_of_not_gt h)
    linarith
  exact hq hji
lemma cost_path (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hs : Standing p q γ c) (hadd : AdditiveCost q c) (i j k : Fin m)
    (hkj : k ≤ j) (hji : j ≤ i) : c i j+c j k=c i k := by
  by_cases hjk : j=k
  · subst k;rw [hs.cost_self];ring
  by_cases hij : i=j
  · subst i;rw [hs.cost_self];ring
  exact hadd i j k (hs.outcome_order (lt_of_le_of_ne hji (Ne.symm hij)))
    (hs.outcome_order (lt_of_le_of_ne hkj (Ne.symm hjk)))
lemma update_policy (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hs : Standing p q γ c) (π : Fin m → ℝ) (hπ : π∈Policies m) (hm : OMPolicy q π)
    (i j : Fin m) (hprev : j.val+1=i.val) (v : ℝ) (hlo : π i ≤ v) (hhi : v ≤ π j) :
    Function.update π i v∈Policies m ∧ OMPolicy q (Function.update π i v) := by
  classical
  have ha := policy_anti q π hs.outcome_order hm
  constructor
  · intro k
    by_cases hki : k=i
    · subst k;simp only [Function.update_self];exact ⟨(hπ i).1.trans hlo,hhi.trans (hπ j).2⟩
    · simpa [Function.update_of_ne hki] using hπ k
  · apply mono_of_anti q _ hs.outcome_order
    intro a b hab
    by_cases hai : a=i
    · subst a
      by_cases hbi : b=i
      · subst b;exact le_rfl
      · rw [Function.update_self,Function.update_of_ne hbi]
        exact (ha hab).trans hlo
    · by_cases hbi : b=i
      · subst b
        rw [Function.update_self,Function.update_of_ne hai]
        have haj : a ≤ j := by apply Fin.le_iff_val_le_val.mpr;have := Fin.le_iff_val_le_val.mp hab;have hne : a.val≠i.val := fun h => hai (Fin.ext h);omega
        exact hhi.trans (ha haj)
      · simpa [Function.update_of_ne hai,Function.update_of_ne hbi] using ha hab
lemma br_update_only (q π : Fin m → ℝ) (c : Fin m → Fin m → ℝ)
    (hq : Function.Injective q) (i : Fin m) (v : ℝ) (hv : π i ≤ v) (r : Fin m)
    (hne : br c q (Function.update π i v) r≠i) :
    br c q (Function.update π i v) r=br c q π r := by
  classical
  let π' := Function.update π i v
  let a := br c q π r
  let b := br c q π' r
  have ho := br_spec c q π r
  have hn := br_spec c q π' r
  have hup (j : Fin m) : π j ≤ π' j := by
    by_cases hji : j=i
    · subst j;simpa [π'] using hv
    · simp [π',Function.update_of_ne hji]
  have hb : π' b=π b := Function.update_of_ne hne _ _
  have hbmax (j : Fin m) : π j-c r j ≤ π b-c r b := by
    have h := hn.1 j
    change π' j-c r j ≤ π' b-c r b at h
    rw [hb] at h
    exact (sub_le_sub_right (hup j) _).trans h
  have hamax (j : Fin m) : π' j-c r j ≤ π' a-c r a := by
    have h := hn.1 j
    have h' := ho.1 b
    change π' j-c r j ≤ π' b-c r b at h
    change π b-c r b ≤ π a-c r a at h'
    rw [hb] at h
    exact h.trans (h'.trans (sub_le_sub_right (hup a) _))
  apply hq
  exact le_antisymm (ho.2 b hbmax) (hn.2 a hamax)
lemma update_improves (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hs : Standing p q γ c) (π : Fin m → ℝ) (hπ : π∈Policies m) (hm : OMPolicy q π)
    (i : Fin m) (v : ℝ) (hv : π i ≤ v) (hg : γ < q i)
    (hresponse : ∀ r,br c q (Function.update π i v) r=i → i ≤ br c q π r) :
    u p q γ c π ≤ u p q γ c (Function.update π i v) := by
  classical
  have ha := policy_anti q π hs.outcome_order hm
  unfold u
  apply Finset.sum_le_sum
  intro r hr
  simp only [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hs.p_nonneg r)
  by_cases hb : br c q (Function.update π i v) r=i
  · rw [hb,Function.update_self]
    have hi := hresponse r hb
    have hq := hs.outcome_order.antitone hi
    have hprob := (ha hi).trans hv
    exact mul_le_mul (sub_le_sub_right hq γ) hprob (hπ _).1 (sub_nonneg.mpr hg.le)
  · have he := br_update_only q π c hs.outcome_order.injective i v hv r hb
    rw [he]
    have hn : br c q π r≠i := by simpa [he] using hb
    rw [Function.update_of_ne hn]
end BinaryResearch
namespace BinaryResearch
open StrategicPolicy.MonotoneBinary
variable {m : ℕ} [NeZero m]
lemma nat_chain {n : ℕ} (a : ℕ → ℝ) (ha : ∀ k < n,a k ≤ a (k+1))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) : a i ≤ a j := by
  induction j,hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hle ih => exact (ih (by omega)).trans (ha j (by omega))
lemma prefix_dominates (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hs : Standing p q γ c) (hadd : AdditiveCost q c) (π : Fin m → ℝ)
    (i : Fin m) (hg : γ < q i) (hh : HighestViolator γ c q π i)
    (a b : Fin m) (hab : a ≤ b) (hbi : b <  i) : π a-c b a ≤ π b := by
  classical
  let f : ℕ → ℝ := fun k => if hk : k < m then π ⟨k,hk⟩+c ⟨k,hk⟩ 0 else 0
  have hf (j : Fin m) : f j.val=π j+c j 0 := by simp [f]
  have hstep (k : ℕ) (hk : k < b.val) : f k ≤ f (k+1) := by
    have hk1 : k+1 < m := by omega
    let s : Fin m := ⟨k,by omega⟩
    let t : Fin m := ⟨k+1,hk1⟩
    have hti : t <  i := by apply Fin.lt_iff_val_lt_val.mpr;dsimp [t];have := Fin.lt_iff_val_lt_val.mp hbi;omega
    have hgain : γ < q t := hg.trans (hs.outcome_order hti)
    have hnon : π s-c t s ≤ π t := by
      by_contra h
      exact hh t s (Fin.lt_iff_val_lt_val.mp hti) ⟨rfl,hgain,Or.inr (lt_of_not_ge h)⟩
    have hcost := cost_path p q γ c hs hadd t s 0 (Fin.zero_le _) (by apply Fin.le_iff_val_le_val.mpr;dsimp [s,t];omega)
    rw [show k=s.val from rfl,hf s,show k+1=t.val from rfl,hf t]
    linarith
  have h := nat_chain f hstep (Fin.le_iff_val_le_val.mp hab) (le_refl b.val)
  rw [hf a,hf b] at h
  have hcost := cost_path p q γ c hs hadd b a 0 (Fin.zero_le _) hab
  linarith
lemma first_raise (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hs : Standing p q γ c) (hc : OMCost q c) (hadd : AdditiveCost q c)
    (π : Fin m → ℝ) (hπ : π∈Policies m) (hm : OMPolicy q π)
    (i j : Fin m) (hprev : j.val+1=i.val) (hg : γ < q i)
    (hh : HighestViolator γ c q π i) (hcase : π j-c i j < π i ∧ π i < π j) :
    u p q γ c π ≤ u p q γ c (Function.update π i (π j)) := by
  have hup := update_policy p q γ c hs π hπ hm i j hprev (π j) hcase.2.le le_rfl
  apply update_improves p q γ c hs π hπ hm i (π j) hcase.2.le hg
  intro r hr
  have hq := nonworsening p q γ c hs hc _ hup.2 r
  rw [hr] at hq
  have hir : i ≤ r := by
    by_contra h
    have := hs.outcome_order (lt_of_not_ge h)
    linarith
  by_contra h
  let a := br c q π r
  have hai : a <  i := lt_of_not_ge h
  have haj : a ≤ j := by apply Fin.le_iff_val_le_val.mpr;have := Fin.lt_iff_val_lt_val.mp hai;omega
  have hji : j <  i := by apply Fin.lt_iff_val_lt_val.mpr;omega
  have hprefix := prefix_dominates p q γ c hs hadd π i hg hh a j haj hji
  have hp1 := cost_path p q γ c hs hadd r i j hji.le hir
  have hp2 := cost_path p q γ c hs hadd r j a haj (hji.le.trans hir)
  have harg := (br_spec c q π r).1 i
  change π i-c r i ≤ π a-c r a at harg
  linarith [hcase.1]
lemma second_raise (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hs : Standing p q γ c) (hc : OMCost q c) (hadd : AdditiveCost q c)
    (π : Fin m → ℝ) (hπ : π∈Policies m) (hm : OMPolicy q π)
    (i j : Fin m) (hprev : j.val+1=i.val) (hg : γ < q i)
    (hcase : π i < π j-c i j) :
    u p q γ c π ≤ u p q γ c (Function.update π i (π j-c i j)) := by
  have hcost0 := cost_nonneg p q γ c hs hc i j
  have hup := update_policy p q γ c hs π hπ hm i j hprev (π j-c i j) hcase.le (by linarith)
  apply update_improves p q γ c hs π hπ hm i (π j-c i j) hcase.le hg
  intro r hr
  have hq := nonworsening p q γ c hs hc _ hup.2 r
  rw [hr] at hq
  have hir : i ≤ r := by
    by_contra h
    have := hs.outcome_order (lt_of_not_ge h)
    linarith
  have hji : j <  i := by apply Fin.lt_iff_val_lt_val.mpr;omega
  have hp := cost_path p q γ c hs hadd r i j hji.le hir
  let π' := Function.update π i (π j-c i j)
  have hn := br_spec c q π' r
  have hmax (l : Fin m) : π' l-c r l ≤ π' j-c r j := by
    have h := hn.1 l
    change π' l-c r l ≤ π' (br c q π' r)-c r (br c q π' r) at h
    rw [hr] at h
    have hpi : π' i=π j-c i j := by simp [π']
    have hpj : π' j=π j := by simp [π',ne_of_lt hji]
    rw [hpi] at h
    rw [hpj]
    linarith
  have hbad := hn.2 j hmax
  rw [hr] at hbad
  exact False.elim ((not_le_of_gt (hs.outcome_order hji)) hbad)
end BinaryResearch

open StrategicPolicy.MonotoneBinary


variable {m : ℕ}

theorem solution [NeZero m]
    (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hstanding : Standing p q γ c) (hcost : OMCost q c)
    (hadd : AdditiveCost q c)
    (πstar : Fin m → ℝ) (hopt : Optimal p q γ c πstar)
    (hmono : OMPolicy q πstar)
    (i j : Fin m) (hprev : j.val + 1 = i.val) (hgain : γ < q i)
    (hhighest : HighestViolator γ c q πstar i)
    (hcase : πstar i < πstar j - c i j) :
    u p q γ c πstar ≤
      u p q γ c (Function.update πstar i (πstar j - c i j)) := by exact BinaryResearch.second_raise p q γ c hstanding hcost hadd πstar hopt.1 hmono i j hprev hgain hcase



#print axioms solution
