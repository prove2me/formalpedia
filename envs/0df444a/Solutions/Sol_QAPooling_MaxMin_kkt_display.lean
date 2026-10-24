-- Prove2me | solution 1 for QAPooling.MaxMin.kkt_display
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:40:06.441978+00:00
-- url     : https://prove2.me/submissions/24e97add-018e-4334-8744-7e95a929eb7f

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model

-- Complete inline local helper: FiniteScore.lean

namespace QAPooling.MaxMin.SavageProof

lemma coe_sum {ι : Type*} (t : Finset ι) (f : ι → ℝ) :
    ((∑ j ∈ t, f j : ℝ) : EReal) = ∑ j ∈ t, (f j : EReal) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [Finset.sum_insert hi, EReal.coe_add, ih]

lemma expectedScore_eq_coe_sum {n : ℕ} (s : ScoringRule n) (p q : Fin n → ℝ)
    (htop : ∀ j, s q j ≠ ⊤) (hzero : ∀ j, s q j = ⊥ → p j = 0) :
    expectedScore s p q = ((∑ j, p j * (s q j).toReal : ℝ) : EReal) := by
  rw [coe_sum]
  unfold expectedScore
  apply Finset.sum_congr rfl
  intro j _
  by_cases hb : s q j = ⊥
  · simp [hzero j hb]
  · rw [EReal.coe_mul, EReal.coe_toReal (htop j) hb]

lemma regular_self_score {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s)
    (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) :
    expectedScore s p p = (expectedReward s p : EReal) := by
  have he := expectedScore_eq_coe_sum s p p (fun j => (hreg p hp j).1)
    (fun j => (hreg p hp j).2)
  unfold expectedReward
  rw [he, EReal.toReal_coe]

lemma reward_eq_sum {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s)
    (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) :
    expectedReward s p = ∑ j, p j * (s p j).toReal := by
  unfold expectedReward
  rw [expectedScore_eq_coe_sum s p p (fun j => (hreg p hp j).1)
    (fun j => (hreg p hp j).2), EReal.toReal_coe]

lemma score_le_reward {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s) (hprop : IsProper s)
    (p q : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) (hq : q ∈ stdSimplex ℝ (Fin n))
    (hzero : ∀ j, s q j = ⊥ → p j = 0) :
    (∑ j, p j * (s q j).toReal) ≤ expectedReward s p := by
  have hh := (hprop p hp q hq).1
  rw [expectedScore_eq_coe_sum s p q (fun j => (hreg q hq j).1) hzero,
    regular_self_score s hreg p hp] at hh
  exact EReal.coe_le_coe_iff.mp hh

end QAPooling.MaxMin.SavageProof


-- Complete inline local helper: SegmentBound.lean

namespace QAPooling.MaxMin.DomainProof

noncomputable def toward {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (t : ℝ) : Fin n → ℝ :=
  (1-t) • x+t • Pi.single j 1

lemma toward_mem {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n))
    (j : Fin n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    toward x j t ∈ stdSimplex ℝ (Fin n) :=
  convex_stdSimplex ℝ (Fin n) hx (single_mem_stdSimplex ℝ j) (by linarith) ht0 (by ring)

lemma toward_score_lower {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s) (hprop : IsProper s)
    (x v : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n))
    (hv : IsSubgradientOn (expectedReward s) v x) (j : Fin n)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ((expectedReward s x+∑ k,v k*((Pi.single j (1 : ℝ) : Fin n → ℝ) k-x k) : ℝ) : EReal) ≤
      s (toward x j t) j := by
  classical
  let q := toward x j t
  have hq : q ∈ stdSimplex ℝ (Fin n) := toward_mem x hx j t ht0.le ht1.le
  have hzero (k : Fin n) (hk : s q k=⊥) : x k=0 := by
    have hh := (hreg q hq k).2 hk
    change (1-t)*x k+t*(Pi.single j (1 : ℝ) : Fin n → ℝ) k=0 at hh
    have he : 0 ≤ (Pi.single j (1 : ℝ) : Fin n → ℝ) k := (single_mem_stdSimplex ℝ j).1 k
    have hm := mul_nonneg ht0.le he
    have hh' : (1-t)*x k=0 := le_antisymm (by linarith) (mul_nonneg (by linarith) (hx.1 k))
    exact (mul_eq_zero.mp hh').resolve_left (by linarith)
  have hqj : 0 < q j := by
    change 0 < (1-t)*x j+t*(Pi.single j (1 : ℝ) : Fin n → ℝ) j
    simp only [Pi.single_eq_same,mul_one]
    have hh := mul_nonneg (show 0 ≤ 1-t by linarith) (hx.1 j)
    linarith
  have hjbot : s q j ≠ ⊥ := by
    intro hh
    have hz := (hreg q hq j).2 hh
    linarith
  have hscore := SavageProof.score_le_reward s hreg hprop x q hx hq hzero
  have he : expectedReward s q=(1-t)*(∑ k,x k*(s q k).toReal)+t*(s q j).toReal := by
    rw [SavageProof.reward_eq_sum s hreg q hq]
    change (∑ k,((1-t)*x k+t*(Pi.single j (1 : ℝ) : Fin n → ℝ) k)*(s q k).toReal)=_
    simp_rw [add_mul,mul_assoc]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    simp [Pi.single_apply,ite_mul]
  have hlo := hv q hq
  have hdot : (∑ k,v k*(q k-x k)) =
      t*∑ k,v k*((Pi.single j (1 : ℝ) : Fin n → ℝ) k-x k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    change v k*((1-t)*x k+t*(Pi.single j (1 : ℝ) : Fin n → ℝ) k-x k)=_
    ring
  rw [hdot] at hlo
  have hbound := mul_le_mul_of_nonneg_left hscore (show 0 ≤ 1-t by linarith)
  have hreal : expectedReward s x+∑ k,v k*((Pi.single j (1 : ℝ) : Fin n → ℝ) k-x k) ≤
      (s q j).toReal := by
    nlinarith
  have hh := EReal.coe_le_coe hreal
  rwa [EReal.coe_toReal (hreg q hq j).1 hjbot] at hh

end QAPooling.MaxMin.DomainProof

-- Complete inline local helper: Domain.lean

namespace QAPooling.MaxMin.DomainProof
open Filter Topology

lemma subgradient_score_lower {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s) (hprop : IsProper s)
    (hcont : ∀ j, ContinuousOn (fun p => s p j) (stdSimplex ℝ (Fin n)))
    (x v : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n))
    (hv : IsSubgradientOn (expectedReward s) v x) (j : Fin n) :
    ((expectedReward s x+∑ k,v k*((Pi.single j (1 : ℝ) : Fin n → ℝ) k-x k) : ℝ) : EReal) ≤
      s x j := by
  have hc : Continuous (toward x j) := by unfold toward; fun_prop
  have hz : toward x j 0=x := by simp [toward]
  have ht : Tendsto (toward x j) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    simpa only [hz] using (hc.tendsto 0).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hi : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 1 :=
    Ioo_mem_nhdsGT (by norm_num)
  have hm : ∀ᶠ t in 𝓝[>] (0 : ℝ), toward x j t ∈ stdSimplex ℝ (Fin n) :=
    hi.mono (fun t ht => toward_mem x hx j t ht.1.le ht.2.le)
  have hs : Tendsto (fun t => s (toward x j t) j) (𝓝[>] (0 : ℝ)) (𝓝 (s x j)) :=
    (hcont j x hx).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (toward x j) ht hm)
  exact ge_of_tendsto hs (hi.mono (fun t ht => toward_score_lower s hreg hprop x v hx hv j t ht.1 ht.2))

lemma finite_subgradient_domain {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s) (hprop : IsProper s)
    (hcont : ∀ j, ContinuousOn (fun p => s p j) (stdSimplex ℝ (Fin n)))
    (x v : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n))
    (hv : IsSubgradientOn (expectedReward s) v x) : x ∈ forecastDomain s := by
  refine ⟨hx,fun j => ⟨?_,(hreg x hx j).1⟩⟩
  intro hb
  have hh := subgradient_score_lower s hreg hprop hcont x v hx hv j
  rw [hb] at hh
  exact (not_le_of_gt (EReal.bot_lt_coe _)) hh

end QAPooling.MaxMin.DomainProof

-- Complete inline local helper: Multipliers.lean

namespace QAPooling.MaxMin.KKTProof

lemma vertex_pairing {n : ℕ} (v x : Fin n → ℝ) (j : Fin n) :
    (∑ k, v k*((Pi.single j (1 : ℝ) : Fin n → ℝ) k-x k)) = v j-∑ k,v k*x k := by
  classical
  simp only [mul_sub,Finset.sum_sub_distrib]
  simp [Pi.single_apply,mul_ite]

lemma multipliers_of_vertex_inequalities {n : ℕ} (x u v : Fin n → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin n))
    (hdir : ∀ j, (∑ k,v k*((Pi.single j (1 : ℝ) : Fin n → ℝ) k-x k)) ≤
      ∑ k,u k*((Pi.single j (1 : ℝ) : Fin n → ℝ) k-x k)) :
    ∃ (lam : ℝ) (mu : Fin n → ℝ),
      (∀ j,u j=v j+lam+mu j) ∧ (∀ j,0 ≤ mu j) ∧ (∀ j,0 < x j → mu j=0) := by
  let d := fun j => u j-v j
  let lam := ∑ j,x j*d j
  let mu := fun j => d j-lam
  have hmean : lam=(∑ j,u j*x j)-(∑ j,v j*x j) := by
    dsimp [lam,d]
    simp_rw [mul_sub,Finset.sum_sub_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  have hmu (j : Fin n) : 0 ≤ mu j := by
    have hh := hdir j
    rw [vertex_pairing,vertex_pairing] at hh
    dsimp [mu,d]
    rw [hmean]
    linarith
  have hsum : (∑ j,x j*mu j)=0 := by
    dsimp [mu]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,hx.2,one_mul]
    exact sub_self lam
  refine ⟨lam,mu,?_,hmu,?_⟩
  · intro j
    dsimp [mu,d]
    ring
  · intro j hj
    have hle := Finset.single_le_sum (s := Finset.univ) (f := fun k => x k*mu k)
      (fun k _ => mul_nonneg (hx.1 k) (hmu k)) (Finset.mem_univ j)
    rw [hsum] at hle
    have he : x j*mu j=0 := le_antisymm hle (mul_nonneg (hx.1 j) (hmu j))
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hj)

end QAPooling.MaxMin.KKTProof

-- Complete inline local helper: Algebra.lean

namespace QAPooling.MaxMin.KKTProof

lemma display_of_score_lower {n : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hreg : IsRegular s) (hg : IsExposure s g) (x v : Fin n → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin n))
    (hscore : ∀ j,
      ((expectedReward s x+∑ k,v k*((Pi.single j (1 : ℝ) : Fin n → ℝ) k-x k) : ℝ) : EReal) ≤ s x j) :
    ∃ (lam : ℝ) (mu : Fin n → ℝ),
      (∀ j,g x j=v j+lam+mu j) ∧ (∀ j,0 ≤ mu j) ∧ (∀ j,0 < x j → mu j=0) := by
  have hxD : x ∈ forecastDomain s := by
    refine ⟨hx,fun j => ⟨?_,(hreg x hx j).1⟩⟩
    exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) (hscore j))
  apply multipliers_of_vertex_inequalities x (g x) v hx
  intro j
  have hh := hscore j
  rw [hg x hxD j] at hh
  have hr := EReal.coe_le_coe_iff.mp hh
  linarith

end QAPooling.MaxMin.KKTProof

namespace QAPooling.MaxMin

theorem _root_.solution {n m : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hreg : IsRegular s) (hprop : IsProper s)
    (hcont : ∀ j, ContinuousOn (fun p => s p j) (stdSimplex ℝ (Fin n)))
    (hGcont : ContinuousOn (expectedReward s) (stdSimplex ℝ (Fin n)))
    (hg : IsExposure s g)
    (p : Fin m → Fin n → ℝ) (hp : ∀ i, p i ∈ forecastDomain s)
    (w : Fin m → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (pstar : Fin n → ℝ) (hpstar : IsQAPool s g p w pstar) :
    ∃ (lam : ℝ) (mu : Fin n → ℝ),
      (∀ j, g pstar j = ∑ i, w i * g (p i) j + lam + mu j) ∧
      (∀ j, 0 ≤ mu j) ∧ (∀ j, 0 < pstar j → mu j = 0) := by
  exact KKTProof.display_of_score_lower s g hreg hg pstar
    (fun j => ∑ i,w i*g (p i) j) hpstar.1
    (DomainProof.subgradient_score_lower s hreg hprop hcont pstar
      (fun j => ∑ i,w i*g (p i) j) hpstar.1 hpstar.2)

end QAPooling.MaxMin
