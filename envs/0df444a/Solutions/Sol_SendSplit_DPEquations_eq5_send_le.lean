-- Prove2me | solution 1 for SendSplit.DPEquations.eq5_send_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:56:58.050339+00:00
-- url     : https://prove2.me/submissions/dbbcd11a-06be-4d81-b6e8-a05c3f7bf703

import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem
import Definitions.Def_SendSplit_DPEquations_Equations



namespace SendSplit.DPEquations

lemma concave_subadd {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : f (a + b) ≤ f a + f b := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h | h
  · have ha' : a = 0 := by linarith
    have hb' : b = 0 := by linarith
    subst ha' hb'; simp [h0]
  · have s1 := hf.2 (Set.mem_Ici.2 (add_nonneg ha hb)) (Set.mem_Ici.2 le_rfl : (0:ℝ) ∈ Set.Ici 0)
      (div_nonneg ha h.le) (sub_nonneg.2 ((div_le_one h).2 (by linarith)) : (0:ℝ) ≤ 1 - a / (a+b))
      (by ring)
    have s2 := hf.2 (Set.mem_Ici.2 (add_nonneg ha hb)) (Set.mem_Ici.2 le_rfl : (0:ℝ) ∈ Set.Ici 0)
      (div_nonneg hb h.le) (sub_nonneg.2 ((div_le_one h).2 (by linarith)) : (0:ℝ) ≤ 1 - b / (a+b))
      (by ring)
    simp only [smul_eq_mul, h0, mul_zero, add_zero] at s1 s2
    have e1 : a / (a + b) * (a + b) = a := by field_simp
    have e2 : b / (a + b) * (a + b) = b := by field_simp
    rw [e1] at s1; rw [e2] at s2
    have e3 : a / (a+b) + b / (a+b) = 1 := by field_simp
    have s3 : (a / (a+b) + b / (a+b)) * f (a+b) ≤ f a + f b := by rw [add_mul]; linarith
    rwa [e3, one_mul] at s3

theorem ereal_le_add_iInf {ι : Sort*} (M : EReal) (s : ℝ) (f : ι → EReal)
    (h : ∀ i, M ≤ (s:EReal) + f i) : M ≤ (s:EReal) + ⨅ i, f i := by
  have h2 : ∀ i, M - s ≤ f i := fun i => EReal.sub_le_of_le_add' (h i)
  have := le_iInf h2
  have h3 := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot s)) (Or.inl (EReal.coe_ne_top s))).1 this
  rwa [add_comm] at h3

lemma flowCost_add_le {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost A c) (x y : Fin n → Fin n → ℝ) (hx : IsPreflow A x)
    (hy : IsPreflow A y) : flowCost A c (x + y) ≤ flowCost A c x + flowCost A c y := by
  unfold flowCost
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p hp => ?_
  have := concave_subadd (hc p hp).1 (hc p hp).2 (hx.1 p.1 p.2) (hy.1 p.1 p.2)
  simpa using this

lemma flow_add_arc {n : ℕ} (A : Finset (Fin n × Fin n)) (d : Fin n → ℝ)
    (x : Fin n → Fin n → ℝ) (hx : IsFlow A d x) (u v : Fin n) (huv : (u, v) ∈ A) (t : ℝ)
    (ht : 0 ≤ t) :
    IsFlow A (fun k => d k + ((if k = v then t else 0) - (if k = u then t else 0)))
      (x + fun a b => if a = u ∧ b = v then t else 0) := by
  classical
  refine ⟨⟨fun a b => ?_, fun a b hab => ?_⟩, fun k => ?_⟩
  · simp only [Pi.add_apply]
    refine add_nonneg (hx.1.1 a b) ?_
    split_ifs <;> simp [ht]
  · have h1 := hx.1.2 a b hab
    have h2 : ¬ (a = u ∧ b = v) := by
      rintro ⟨rfl, rfl⟩; exact hab huv
    simp [h1, h2]
  · have hk := hx.2 k
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    have hin : ∑ j ∈ Finset.univ.filter (fun j => (j, k) ∈ A), (if j = u ∧ k = v then t else 0)
        = if k = v then t else 0 := by
      by_cases hkv : k = v
      · subst hkv
        rw [Finset.sum_eq_single u]
        · simp
        · intro b _ hb; simp [hb]
        · intro hu; simp [huv] at hu
      · simp [hkv]
    have hout : ∑ kk ∈ Finset.univ.filter (fun kk => (k, kk) ∈ A), (if k = u ∧ kk = v then t else 0)
        = if k = u then t else 0 := by
      by_cases hku : k = u
      · subst hku
        rw [Finset.sum_eq_single v]
        · simp
        · intro b _ hb; simp [hb]
        · intro hu; simp [huv] at hu
      · simp [hku]
    rw [hin, hout]
    linarith

lemma sendCost_step {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost A c) (d : Fin n → ℝ) (x : Fin n → Fin n → ℝ) (hx : IsFlow A d x)
    (u v : Fin n) (huv : (u, v) ∈ A) (t : ℝ) (ht : 0 ≤ t) (d' : Fin n → ℝ)
    (hd : d' = fun k => d k + ((if k = v then t else 0) - (if k = u then t else 0))) :
    ∃ x', IsFlow A d' x' ∧ flowCost A c x' ≤ c u v t + flowCost A c x := by
  subst hd
  classical
  refine ⟨_, flow_add_arc A d x hx u v huv t ht, ?_⟩
  have hy : IsPreflow A (fun a b => if a = u ∧ b = v then t else 0) := by
    refine ⟨fun a b => ?_, fun a b hab => ?_⟩
    · show 0 ≤ (if a = u ∧ b = v then t else 0)
      split_ifs <;> simp [ht]
    · have h2 : ¬ (a = u ∧ b = v) := by
        rintro ⟨rfl, rfl⟩; exact hab huv
      simp [h2]
  refine (flowCost_add_le A c hc x _ hx.1 hy).trans ?_
  have : flowCost A c (fun a b => if a = u ∧ b = v then t else 0) = c u v t := by
    unfold flowCost
    rw [Finset.sum_eq_single (u, v)]
    · simp
    · intro p hp hne
      have : ¬ (p.1 = u ∧ p.2 = v) := fun h => hne (Prod.ext h.1 h.2)
      simp [this, (hc p hp).2]
    · intro h; exact absurd huv h
  rw [this]; linarith

theorem eq1_core {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (i : Fin n) (I : Finset (Fin n)) (hrI : demandSum r I = 0)
    (j : Fin n) (hj : j ∈ I) :
    minCost A c r i I = minCost A c r j (I.erase j) := by
  have h : subDemand r i I = subDemand r j (I.erase j) := by
    funext k
    have hs : demandSum r (I.erase j) = - r j := by
      unfold demandSum at hrI ⊢
      rw [Finset.sum_erase_eq_sub hj, hrI]; ring
    unfold subDemand
    rw [hs, hrI]
    by_cases hkj : k = j
    · subst hkj; simp [hj]
    · simp [hkj, Finset.mem_erase]
  unfold minCost
  rw [h]

theorem eq4_core {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hc : IsConcaveArcCost A c)
    (i : Fin n) (I : Finset (Fin n))
    (x y : Fin n → Fin n → ℝ) (hx : IsPreflow A x) (hy : IsPreflow A y)
    (hxy : IsFlow A (subDemand r i I) (x + y)) :
    minCost A c r i I ≤ ((flowCost A c x + flowCost A c y : ℝ) : EReal) := by
  unfold minCost
  refine (iInf₂_le (x + y) hxy).trans ?_
  exact EReal.coe_le_coe_iff.2 (flowCost_add_le A c hc x y hx hy)

theorem eq5_core {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (i j : Fin n) (I : Finset (Fin n))
    (hij : IsSendArc A r I i j) :
    minCost A c r i I ≤ sendCost A c r I i j + minCost A c r j I := by
  have key : ∀ (u v : Fin n) (t : ℝ), (u, v) ∈ A → 0 ≤ t →
      (subDemand r i I = fun k => subDemand r j I k + ((if k = v then t else 0) - (if k = u then t else 0))) →
      minCost A c r i I ≤ ((c u v t : ℝ) : EReal) + minCost A c r j I := by
    intro u v t huv ht hd
    have e : minCost A c r j I = ⨅ x : Fin n → Fin n → ℝ, ⨅ (_ : IsFlow A (subDemand r j I) x),
        ((flowCost A c x : ℝ) : EReal) := rfl
    rw [e]
    apply ereal_le_add_iInf
    intro x
    apply ereal_le_add_iInf
    intro hx
    obtain ⟨x', hx', hle⟩ := sendCost_step A c hc _ x hx u v huv t ht _ hd
    have h1 : minCost A c r i I ≤ ((flowCost A c x' : ℝ) : EReal) := iInf₂_le x' hx'
    refine h1.trans ?_
    rw [← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2 hle
  rcases hij with ⟨hpos, hA'⟩ | ⟨hneg, hA'⟩
  · have hne : i ≠ j := hA _ hA'
    unfold sendCost
    rw [if_pos ⟨hpos, hA'⟩]
    refine key i j (demandSum r I) hA' hpos.le ?_
    funext k
    unfold subDemand
    by_cases hki : k = i
    · subst hki; simp [hne]; ring
    · by_cases hkj : k = j
      · subst hkj; simp [hki]
      · simp [hki, hkj]
  · have hne : j ≠ i := hA _ hA'
    have hnp : ¬ 0 < demandSum r I := not_lt.2 hneg.le
    unfold sendCost
    rw [if_neg (fun h => hnp h.1), if_pos ⟨hneg, hA'⟩]
    refine key j i (-demandSum r I) hA' (by linarith) ?_
    funext k
    unfold subDemand
    by_cases hki : k = i
    · subst hki; simp [hne.symm]; ring
    · by_cases hkj : k = j
      · subst hkj; simp [hki]
      · simp [hki, hkj]

end SendSplit.DPEquations

open SendSplit.DPEquations


theorem solution {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (i j : Fin n) (I : Finset (Fin n)) (hI : IsAdmissible r I)
    (hij : IsSendArc A r I i j) :
    minCost A c r i I ≤ sendCost A c r I i j + minCost A c r j I := by
  exact eq5_core A c r hA hc i j I hij
