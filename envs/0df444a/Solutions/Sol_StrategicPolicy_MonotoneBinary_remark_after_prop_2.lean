-- Prove2me | solution 1 for StrategicPolicy.MonotoneBinary.remark_after_prop_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T11:35:09.420486+00:00
-- url     : https://prove2.me/submissions/67ace7d3-12aa-4691-85d1-90af9d72a273

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

open StrategicPolicy.MonotoneBinary


variable {m : ℕ}

theorem solution [NeZero m]
    (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hstanding : Standing p q γ c) (hcost : OMCost q c)
    (π : Fin m → ℝ) (hπ : π ∈ Policies m) (hmono : OMPolicy q π) :
    ∀ i, q i ≤ q (br c q π i) := by exact BinaryResearch.nonworsening p q γ c hstanding hcost π hmono



#print axioms solution
