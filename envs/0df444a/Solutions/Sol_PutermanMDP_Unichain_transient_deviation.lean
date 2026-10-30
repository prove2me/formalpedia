-- Prove2me | solution 1 for PutermanMDP.Unichain.transient_deviation
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T14:53:34.567479+00:00
-- url     : https://prove2.me/submissions/d2bb7d03-258b-4360-b990-c6445de1f800

import Mathlib
import Definitions.Def_PutermanMDP_Unichain_Iteration
section
set_option autoImplicit false

open MarkovDecisionProcesses in
theorem p016_acc_closed {S : Type*} {P : S → S → ℝ} {T : S → Prop}
    (hT : ∀ i j, T i → 0 < P i j → T j) {i j : S} (hi : T i) (h : Accessible P i j) : T j := by
  unfold Accessible at h
  induction h with
  | refl => exact hi
  | tail _ hbc ih => exact hT _ _ ih hbc

open MarkovDecisionProcesses in
theorem p016_acc_transfer {S : Type*} {P Q : S → S → ℝ} {T : S → Prop}
    (hT : ∀ i j, T i → 0 < P i j → T j) (hPQ : ∀ i, T i → ∀ j, P i j = Q i j)
    {i j : S} (hi : T i) (h : Accessible P i j) : Accessible Q i j := by
  unfold Accessible at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      exact ih.tail (by rw [← hPQ _ (p016_acc_closed hT hi hab)]; exact hbc)

open MarkovDecisionProcesses in
theorem p016_exists_recurrent {S : Type*} [Fintype S] (P : S → S → ℝ) (i : S) :
    ∃ j, Accessible P i j ∧ IsRecurrent P j := by
  classical
  let acc : S → Finset S := fun x => Finset.univ.filter (fun y => Accessible P x y)
  have hi : i ∈ acc i := by
    simp only [acc, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  obtain ⟨j, hj, hmin⟩ := (acc i).exists_min_image (fun x => (acc x).card) ⟨i, hi⟩
  have hij : Accessible P i j := by
    simpa only [acc, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  refine ⟨j, hij, ?_⟩
  intro k hjk
  have hsub : acc k ⊆ acc j := by
    intro y hy
    simp only [acc, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact Relation.ReflTransGen.trans hjk hy
  have hk : k ∈ acc i := by
    simp only [acc, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.trans hij hjk
  have hcard := hmin k hk
  have heq : acc k = acc j := Finset.eq_of_subset_of_card_le hsub hcard
  have hjj : j ∈ acc j := by
    simp only [acc, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  rw [← heq] at hjj
  simpa only [acc, Finset.mem_filter, Finset.mem_univ, true_and] using hjj

open MarkovDecisionProcesses in
theorem p016_closed_mem_recurrent {S : Type*} [Fintype S] {P : S → S → ℝ}
    (hU : IsUnichainMatrix P) {T : S → Prop} (hT : ∀ i j, T i → 0 < P i j → T j)
    {i s0 : S} (hi : T i) (hs0 : IsRecurrent P s0) : T s0 := by
  obtain ⟨j, hij, hj⟩ := p016_exists_recurrent P i
  exact p016_acc_closed hT (p016_acc_closed hT hi hij) (hU j s0 hj hs0)

theorem p016_min_principle {S : Type*} [Fintype S] {P : S → S → ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) {u : S → ℝ} {s : S}
    (hmin : ∀ j, u s ≤ u j) (hle : ∑ j, P s j * u j ≤ u s) :
    ∀ j, 0 < P s j → u j = u s := by
  have hnn : ∀ j ∈ (Finset.univ : Finset S), 0 ≤ P s j * (u j - u s) :=
    fun j _ => mul_nonneg (hP0 s j) (sub_nonneg.2 (hmin j))
  have hsum : ∑ j, P s j * (u j - u s) = 0 := by
    have h1 : ∑ j, P s j * (u j - u s) = ∑ j, P s j * u j - u s := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hP1 s, one_mul]
    have hge : 0 ≤ ∑ j, P s j * (u j - u s) := Finset.sum_nonneg hnn
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
  intro j hj
  have := hz j (Finset.mem_univ j)
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

theorem p016_avg_ge {S : Type*} [Fintype S] {P : S → S → ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) {u : S → ℝ} {c : ℝ} (s : S)
    (hmin : ∀ j, c ≤ u j) : c ≤ ∑ j, P s j * u j := by
  have : ∑ j, P s j * c ≤ ∑ j, P s j * u j :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hmin j) (hP0 s j))
  rwa [← Finset.sum_mul, hP1 s, one_mul] at this

theorem p016_avg_ge_min {S : Type*} [Fintype S] {P : S → S → ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) {u : S → ℝ} {s : S}
    (hmin : ∀ j, u s ≤ u j) : u s ≤ ∑ j, P s j * u j :=
  p016_avg_ge hP0 hP1 s hmin

open MarkovDecisionProcesses in
theorem p016_poisson {S : Type*} [Fintype S] {P : S → S → ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) (hU : IsUnichainMatrix P)
    (r : S → ℝ) : ∃ (g : ℝ) (h : S → ℝ), ∀ s, g + h s = r s + ∑ j, P s j * h j := by
  classical
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨0, 0, fun s => (IsEmpty.false s).elim⟩
  let L : (ℝ × (S → ℝ)) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun p s => p.1 + p.2 s - ∑ j, P s j * p.2 j
      map_add' := by
        intro p q; ext s
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro c p; ext s
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [show ∑ j, P s j * (c * p.2 j) = c * ∑ j, P s j * p.2 j by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)]
        ring }
  have hL : ∀ p : ℝ × (S → ℝ), ∀ s, L p s = p.1 + p.2 s - ∑ j, P s j * p.2 j := fun _ _ => rfl
  have hker : LinearMap.ker L ≤ Submodule.span ℝ {((0:ℝ), (fun _ : S => (1:ℝ)))} := by
    intro p hp
    rw [LinearMap.mem_ker] at hp
    have hp' : ∀ s, p.1 + p.2 s = ∑ j, P s j * p.2 j := by
      intro s; have := congrFun hp s; rw [hL] at this; simp only [Pi.zero_apply] at this; linarith
    obtain ⟨s1, hs1⟩ := Finite.exists_min p.2
    obtain ⟨s2, hs2⟩ := Finite.exists_max p.2
    have hg1 : 0 ≤ p.1 := by
      have := p016_avg_ge_min hP0 hP1 hs1; have := hp' s1; linarith
    have hneg : ∀ i, ∑ j, P i j * (fun k => - p.2 k) j = - ∑ j, P i j * p.2 j := by
      intro i; simp only [mul_neg, Finset.sum_neg_distrib]
    have hg2 : p.1 ≤ 0 := by
      have h1 := p016_avg_ge_min hP0 hP1 (u := fun k => - p.2 k) (s := s2)
        (fun j => by simp only [neg_le_neg_iff]; exact hs2 j)
      rw [hneg] at h1
      have := hp' s2; linarith
    have hg : p.1 = 0 := le_antisymm hg2 hg1
    have hTmin : ∀ i j, p.2 i = p.2 s1 → 0 < P i j → p.2 j = p.2 s1 := by
      intro i j hi hij
      have hmin' : ∀ k, p.2 i ≤ p.2 k := fun k => hi ▸ hs1 k
      have := p016_min_principle hP0 hP1 hmin' (by have := hp' i; linarith) j hij
      rw [this, hi]
    have hTmax : ∀ i j, p.2 i = p.2 s2 → 0 < P i j → p.2 j = p.2 s2 := by
      intro i j hi hij
      have hmin' : ∀ k, (fun k => - p.2 k) i ≤ (fun k => - p.2 k) k := fun k => by
        simp only [neg_le_neg_iff]; rw [hi]; exact hs2 k
      have := p016_min_principle hP0 hP1 hmin'
        (by rw [hneg]; have := hp' i; linarith) j hij
      simp only [neg_inj] at this; rw [this, hi]
    obtain ⟨t, -, ht⟩ := p016_exists_recurrent P s1
    have h1 := p016_closed_mem_recurrent hU (T := fun i => p.2 i = p.2 s1) hTmin rfl ht
    have h2 := p016_closed_mem_recurrent hU (T := fun i => p.2 i = p.2 s2) hTmax rfl ht
    have hconst : ∀ k, p.2 k = p.2 s1 := fun k =>
      le_antisymm (by have := hs2 k; linarith) (hs1 k)
    rw [Submodule.mem_span_singleton]
    refine ⟨p.2 s1, ?_⟩
    ext
    · simp [hg]
    · simp [hconst]
  have hne : ((0:ℝ), (fun _ : S => (1:ℝ))) ≠ (0 : ℝ × (S → ℝ)) := by
    intro h
    obtain ⟨s⟩ := hS
    have := congrFun (congrArg Prod.snd h) s
    simp at this
  have hfk : Module.finrank ℝ (LinearMap.ker L) ≤ 1 := by
    calc Module.finrank ℝ (LinearMap.ker L)
        ≤ Module.finrank ℝ (Submodule.span ℝ {((0:ℝ), (fun _ : S => (1:ℝ)))}) :=
          Submodule.finrank_mono hker
      _ = 1 := finrank_span_singleton hne
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at hrn
  have hle := Submodule.finrank_le (LinearMap.range L)
  rw [Module.finrank_fintype_fun_eq_card] at hle
  have htop : LinearMap.range L = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  obtain ⟨p, hp⟩ : r ∈ LinearMap.range L := by rw [htop]; exact Submodule.mem_top
  refine ⟨p.1, p.2, fun s => ?_⟩
  have := congrFun hp s
  rw [hL] at this
  linarith

open MarkovDecisionProcesses in
theorem p016_exists_solution {S A : Type*} [Fintype S] [Fintype A] (M : StationaryMDP S A)
    (hM : IsUnichain M) : ∃ (g : ℝ) (h : S → ℝ),
      (∀ s, ∀ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j ≤ g + h s) ∧
      (∀ s, ∃ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j = g + h s) := by
  classical
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨0, 0, fun s => (IsEmpty.false s).elim, fun s => (IsEmpty.false s).elim⟩
  have hP0 : ∀ d : S → A, ∀ i j, 0 ≤ transMatrix M d i j := fun d i j => M.trans_nonneg _ _ _
  have hP1 : ∀ d : S → A, ∀ i, ∑ j, transMatrix M d i j = 1 := fun d i => M.trans_sum _ _
  have hpois : ∀ d : S → A, ∃ (g : ℝ) (h : S → ℝ), (∀ s, d s ∈ M.admissible s) →
      ∀ s, g + h s = M.reward s (d s) + ∑ j, M.trans s (d s) j * h j := by
    intro d
    by_cases hd : ∀ s, d s ∈ M.admissible s
    · obtain ⟨g, h, hgh⟩ := p016_poisson (hP0 d) (hP1 d) (hM d hd) (fun s => M.reward s (d s))
      exact ⟨g, h, fun _ => hgh⟩
    · exact ⟨0, 0, fun h => (hd h).elim⟩
  choose G H hGH using hpois
  let D : Finset (S → A) := Finset.univ.filter (fun d => ∀ s, d s ∈ M.admissible s)
  let d0 : S → A := fun s => (M.admissible_nonempty s).choose
  have hd0 : d0 ∈ D := by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun s => (M.admissible_nonempty s).choose_spec
  let gs : ℝ := D.sup' ⟨d0, hd0⟩ G
  obtain ⟨d1, hd1D, hd1G⟩ := Finset.exists_mem_eq_sup' ⟨d0, hd0⟩ G
  obtain ⟨s0, -, hs0⟩ := p016_exists_recurrent (transMatrix M d1) hS.some
  let D0 : Finset (S → A) := D.filter (fun d => G d = gs ∧ IsRecurrent (transMatrix M d) s0)
  have hd1 : d1 ∈ D0 := by
    simp only [D0, Finset.mem_filter]
    exact ⟨hd1D, hd1G.symm, hs0⟩
  let Φ : (S → A) → ℝ := fun d => ∑ s, (H d s - H d s0)
  obtain ⟨d, hdD0, hdmax⟩ := D0.exists_max_image Φ ⟨d1, hd1⟩
  simp only [D0, D, Finset.mem_filter, Finset.mem_univ, true_and] at hdD0
  obtain ⟨hdadm, hdG, hdrec⟩ := hdD0
  have hpd := hGH d hdadm
  rw [hdG] at hpd
  refine ⟨gs, H d, ?_, fun s => ⟨d s, hdadm s, (hpd s).symm⟩⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨sv, av, hav, hviol⟩ := hcon
  let viol : S → A → Prop := fun s a =>
    a ∈ M.admissible s ∧ gs + H d s < M.reward s a + ∑ j, M.trans s a j * H d j
  let d' : S → A := fun s => if hs : ∃ a, viol s a then hs.choose else d s
  have hd'viol : ∀ s, (∃ a, viol s a) → viol s (d' s) := by
    intro s hs; simp only [d', dif_pos hs]; exact hs.choose_spec
  have hd'eq : ∀ s, ¬ (∃ a, viol s a) → d' s = d s := by
    intro s hs; simp only [d', dif_neg hs]
  have hd'adm : ∀ s, d' s ∈ M.admissible s := by
    intro s
    by_cases hs : ∃ a, viol s a
    · exact (hd'viol s hs).1
    · rw [hd'eq s hs]; exact hdadm s
  let δ : S → ℝ := fun s =>
    M.reward s (d' s) + ∑ j, M.trans s (d' s) j * H d j - gs - H d s
  have hδpos : ∀ s, (∃ a, viol s a) → 0 < δ s := by
    intro s hs; have := (hd'viol s hs).2; simp only [δ]; linarith
  have hδz : ∀ s, ¬ (∃ a, viol s a) → δ s = 0 := by
    intro s hs; simp only [δ]; rw [hd'eq s hs]; have := hpd s; linarith
  have hδnn : ∀ s, 0 ≤ δ s := by
    intro s; by_cases hs : ∃ a, viol s a
    · exact (hδpos s hs).le
    · exact (hδz s hs).ge
  have hsv : ∃ a, viol sv a := ⟨av, hav, hviol⟩
  have hpd' := hGH d' hd'adm
  have hd'D : d' ∈ D := by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]; exact hd'adm
  have hG'le : G d' ≤ gs := Finset.le_sup' G hd'D
  let u : S → ℝ := fun s => H d' s - H d s
  let P' := transMatrix M d'
  have hu : ∀ s, (G d' - gs) + u s = δ s + ∑ j, P' s j * u j := by
    intro s
    have e1 := hpd' s
    have e2 : ∑ j, P' s j * u j =
        ∑ j, M.trans s (d' s) j * H d' j - ∑ j, M.trans s (d' s) j * H d j := by
      simp only [P', u, transMatrix, mul_sub, Finset.sum_sub_distrib]
    rw [e2]; simp only [δ, u]; linarith
  obtain ⟨s1, hs1⟩ := Finite.exists_min u
  have hGge : gs ≤ G d' := by
    have := hu s1
    have := p016_avg_ge_min (hP0 d') (hP1 d') hs1
    have := hδnn s1
    linarith
  have hGeq : G d' = gs := le_antisymm hG'le hGge
  have hu' : ∀ s, u s = δ s + ∑ j, P' s j * u j := by
    intro s; have := hu s; rw [hGeq] at this; linarith
  let T : S → Prop := fun i => u i = u s1
  have hTδ : ∀ i, T i → δ i = 0 := by
    intro i hi
    have h1 := hu' i
    have h2 := p016_avg_ge (hP0 d') (hP1 d') (u := u) i hs1
    have h3 := hδnn i
    have h4 : u i = u s1 := hi
    linarith
  have hTd : ∀ i, T i → d' i = d i := by
    intro i hi
    by_cases hs : ∃ a, viol i a
    · exact absurd (hTδ i hi) (hδpos i hs).ne'
    · exact hd'eq i hs
  have hTclosed' : ∀ i j, T i → 0 < P' i j → T j := by
    intro i j hi hij
    have h4 : u i = u s1 := hi
    have hmin' : ∀ k, u i ≤ u k := fun k => h4.trans_le (hs1 k)
    have := p016_min_principle (hP0 d') (hP1 d') hmin'
      (by have := hu' i; have := hTδ i hi; linarith) j hij
    show u j = u s1
    rw [this]; exact hi
  have hrows : ∀ i, T i → ∀ j, P' i j = transMatrix M d i j := by
    intro i hi j; simp only [P', transMatrix, hTd i hi]
  have hTclosed : ∀ i j, T i → 0 < transMatrix M d i j → T j := by
    intro i j hi hij; exact hTclosed' i j hi (by rw [hrows i hi]; exact hij)
  have hs0T : T s0 :=
    p016_closed_mem_recurrent (hM d hdadm) hTclosed (show T s1 from rfl) hdrec
  have hs0rec' : IsRecurrent P' s0 := by
    intro j hj
    have h1 : Accessible (transMatrix M d) s0 j := p016_acc_transfer hTclosed' hrows hs0T hj
    have h2 := hdrec j h1
    have hjT : T j := p016_acc_closed hTclosed' hs0T hj
    exact p016_acc_transfer hTclosed (fun i hi k => (hrows i hi k).symm) hjT h2
  have hd'D0 : d' ∈ D0 := by
    simp only [D0, D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hd'adm, hGeq, hs0rec'⟩
  have hmax := hdmax d' hd'D0
  have h0 : u s0 = u s1 := hs0T
  have hlt : Φ d < Φ d' := by
    show ∑ s, (H d s - H d s0) < ∑ s, (H d' s - H d' s0)
    apply Finset.sum_lt_sum
    · intro s _
      have := hs1 s
      simp only [u] at this h0
      linarith
    · refine ⟨sv, Finset.mem_univ _, ?_⟩
      have h1 := hu' sv
      have h2 := p016_avg_ge (hP0 d') (hP1 d') (u := u) sv hs1
      have h3 := hδpos sv hsv
      simp only [u] at h1 h2 h0
      linarith
  linarith

open MarkovDecisionProcesses in
theorem p016_tr_upper {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (π : AvgHRPolicy M) (g : ℝ) (h : S → ℝ) (m : ℝ) (hm : ∀ j, m ≤ h j)
    (hB : ∀ s, ∀ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j ≤ g + h s) :
    ∀ (N t : ℕ) (hist : List (S × A)) (s : S), totalReward π N t hist s ≤ N * g + h s - m := by
  intro N
  induction N with
  | zero =>
    intro t hist s
    simp only [totalReward, Nat.cast_zero, zero_mul, zero_add]
    linarith [hm s]
  | succ k ih =>
    intro t hist s
    simp only [totalReward]
    calc ∑ a ∈ M.admissible s, π.q t hist s a *
          (M.reward s a + ∑ j, M.trans s a j * totalReward π k (t+1) (hist ++ [(s,a)]) j)
        ≤ ∑ a ∈ M.admissible s, π.q t hist s a * (((k+1:ℕ):ℝ) * g + h s - m) := by
          apply Finset.sum_le_sum; intro a ha
          apply mul_le_mul_of_nonneg_left _ (π.nonneg t hist s a)
          have h1 : ∑ j, M.trans s a j * totalReward π k (t+1) (hist ++ [(s,a)]) j
              ≤ ∑ j, M.trans s a j * ((k:ℝ) * g + h j - m) :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (ih _ _ j) (M.trans_nonneg s a j))
          have h2 : ∑ j, M.trans s a j * ((k:ℝ) * g + h j - m)
              = ((k:ℝ) * g - m) + ∑ j, M.trans s a j * h j := by
            have e : ∀ j, M.trans s a j * ((k:ℝ) * g + h j - m)
                = M.trans s a j * ((k:ℝ) * g - m) + M.trans s a j * h j := fun j => by ring
            simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, M.trans_sum, one_mul]
          have h3 := hB s a ha
          push_cast; linarith
      _ = ((k+1:ℕ):ℝ) * g + h s - m := by rw [← Finset.sum_mul, π.sum_one, one_mul]

open MarkovDecisionProcesses in
theorem p016_tr_lower {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (π : AvgHRPolicy M) (g : ℝ) (h : S → ℝ) (m : ℝ) (hm : ∀ j, h j ≤ m)
    (hB : ∀ (t : ℕ) (hist : List (S × A)) (s : S) (a : A), a ∈ M.admissible s →
      π.q t hist s a ≠ 0 → g + h s ≤ M.reward s a + ∑ j, M.trans s a j * h j) :
    ∀ (N t : ℕ) (hist : List (S × A)) (s : S), (N:ℝ) * g + h s - m ≤ totalReward π N t hist s := by
  intro N
  induction N with
  | zero =>
    intro t hist s
    simp only [totalReward, Nat.cast_zero, zero_mul, zero_add]
    linarith [hm s]
  | succ k ih =>
    intro t hist s
    simp only [totalReward]
    calc ((k+1:ℕ):ℝ) * g + h s - m
        = ∑ a ∈ M.admissible s, π.q t hist s a * (((k+1:ℕ):ℝ) * g + h s - m) := by
          rw [← Finset.sum_mul, π.sum_one, one_mul]
      _ ≤ ∑ a ∈ M.admissible s, π.q t hist s a *
          (M.reward s a + ∑ j, M.trans s a j * totalReward π k (t+1) (hist ++ [(s,a)]) j) := by
          apply Finset.sum_le_sum; intro a ha
          by_cases hq : π.q t hist s a = 0
          · rw [hq, zero_mul, zero_mul]
          apply mul_le_mul_of_nonneg_left _ (π.nonneg t hist s a)
          have h1 : ∑ j, M.trans s a j * ((k:ℝ) * g + h j - m)
              ≤ ∑ j, M.trans s a j * totalReward π k (t+1) (hist ++ [(s,a)]) j :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (ih _ _ j) (M.trans_nonneg s a j))
          have h2 : ∑ j, M.trans s a j * ((k:ℝ) * g + h j - m)
              = ((k:ℝ) * g - m) + ∑ j, M.trans s a j * h j := by
            have e : ∀ j, M.trans s a j * ((k:ℝ) * g + h j - m)
                = M.trans s a j * ((k:ℝ) * g - m) + M.trans s a j * h j := fun j => by ring
            simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, M.trans_sum, one_mul]
          have h3 := hB t hist s a ha hq
          push_cast; linarith

open MarkovDecisionProcesses in
theorem p016_gain_bounds {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (π : AvgHRPolicy M) (s : S) : ∃ R : ℝ, ∀ N : ℕ,
      -R ≤ totalReward π N 0 [] s / N ∧ totalReward π N 0 [] s / N ≤ R := by
  let R : ℝ := ∑ s, ∑ a, |M.reward s a|
  have hR : ∀ s a, |M.reward s a| ≤ R := by
    intro s a
    calc |M.reward s a| ≤ ∑ a, |M.reward s a| :=
          Finset.single_le_sum (f := fun a => |M.reward s a|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ a)
      _ ≤ R := Finset.single_le_sum (f := fun s => ∑ a, |M.reward s a|)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ s)
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hup := p016_tr_upper π R (fun _ => 0) 0 (fun _ => le_refl 0) (by
    intro s a _
    simp only [mul_zero, Finset.sum_const_zero, add_zero]
    exact (le_abs_self _).trans (hR s a))
  have hlo := p016_tr_lower π (-R) (fun _ => 0) 0 (fun _ => le_refl 0) (by
    intro t hist s a _ _
    simp only [mul_zero, Finset.sum_const_zero, add_zero]
    exact (neg_le_neg (hR s a)).trans (neg_abs_le _))
  refine ⟨R, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [hR0]
  · have hNpos : (0:ℝ) < N := Nat.cast_pos.2 hN
    have h1 := hup N 0 [] s
    have h2 := hlo N 0 [] s
    simp only [add_zero, sub_zero] at h1 h2
    constructor
    · rw [le_div_iff₀ hNpos]; linarith
    · rw [div_le_iff₀ hNpos]; linarith

open MarkovDecisionProcesses in
theorem p016_gainSup_le {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (π : AvgHRPolicy M) (s : S) (g C : ℝ)
    (hC : ∀ N : ℕ, totalReward π N 0 [] s ≤ N * g + C) : gainSup π s ≤ g := by
  obtain ⟨R, hR⟩ := p016_gain_bounds π s
  unfold gainSup
  have hv : Filter.Tendsto (fun N : ℕ => g + C / N) Filter.atTop (nhds g) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat C)
  calc Filter.limsup (fun N : ℕ => totalReward π N 0 [] s / N) Filter.atTop
      ≤ Filter.limsup (fun N : ℕ => g + C / N) Filter.atTop := by
        refine Filter.limsup_le_limsup ?_ ?_ ?_
        · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
          have hNpos : (0:ℝ) < N := by exact_mod_cast hN
          rw [div_le_iff₀ hNpos, add_mul, div_mul_cancel₀ _ hNpos.ne']
          linarith [hC N]
        · exact Filter.isCoboundedUnder_le_of_le Filter.atTop (fun N => (hR N).1)
        · exact hv.isBoundedUnder_le
    _ = g := hv.limsup_eq

open MarkovDecisionProcesses in
theorem p016_le_gainInf {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (π : AvgHRPolicy M) (s : S) (g C : ℝ)
    (hC : ∀ N : ℕ, (N:ℝ) * g - C ≤ totalReward π N 0 [] s) : g ≤ gainInf π s := by
  obtain ⟨R, hR⟩ := p016_gain_bounds π s
  unfold gainInf
  have hv : Filter.Tendsto (fun N : ℕ => g - C / N) Filter.atTop (nhds g) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat C)
  calc g = Filter.liminf (fun N : ℕ => g - C / N) Filter.atTop := hv.liminf_eq.symm
    _ ≤ Filter.liminf (fun N : ℕ => totalReward π N 0 [] s / N) Filter.atTop := by
        refine Filter.liminf_le_liminf ?_ ?_ ?_
        · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
          have hNpos : (0:ℝ) < N := by exact_mod_cast hN
          rw [le_div_iff₀ hNpos, sub_mul, div_mul_cancel₀ _ hNpos.ne']
          linarith [hC N]
        · exact hv.isBoundedUnder_ge
        · exact Filter.isCoboundedUnder_ge_of_le Filter.atTop (fun N => (hR N).2)

open MarkovDecisionProcesses in
theorem p016_inf_le_sup {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (π : AvgHRPolicy M) (s : S) : gainInf π s ≤ gainSup π s := by
  obtain ⟨R, hR⟩ := p016_gain_bounds π s
  exact Filter.liminf_le_limsup (Filter.isBoundedUnder_of ⟨R, fun N => (hR N).2⟩)
    (Filter.isBoundedUnder_of ⟨-R, fun N => (hR N).1⟩)

open MarkovDecisionProcesses in
theorem p016_residual_iff {S A : Type*} [Fintype S] [Fintype A] (M : StationaryMDP S A)
    (g : ℝ) (h : S → ℝ) (s : S) : optimalityResidual M g h s = 0 ↔
      ((∀ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j ≤ g + h s) ∧
       (∃ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j = g + h s)) := by
  unfold optimalityResidual
  constructor
  · intro h0
    refine ⟨fun a ha => ?_, ?_⟩
    · have := Finset.le_sup' (fun a => M.reward s a - g + ∑ j, M.trans s a j * h j - h s) ha
      rw [h0] at this; linarith
    · obtain ⟨a, ha, hae⟩ := Finset.exists_mem_eq_sup' (M.admissible_nonempty s)
        (fun a => M.reward s a - g + ∑ j, M.trans s a j * h j - h s)
      refine ⟨a, ha, ?_⟩
      rw [h0] at hae; linarith
  · rintro ⟨h1, a, ha, hae⟩
    apply le_antisymm
    · apply Finset.sup'_le
      intro b hb; have := h1 b hb; linarith
    · apply Finset.le_sup'_of_le _ ha
      linarith

open MarkovDecisionProcesses in
theorem p016_bounds_of_improving {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]
    {M : StationaryMDP S A} (g : ℝ) (h : S → ℝ)
    (hres : ∀ s, optimalityResidual M g h s = 0) (d : S → A) (hd : IsImproving M h d) :
    (∀ (π : AvgHRPolicy M) (s : S), gainSup π s ≤ g) ∧
      (∀ s, g ≤ gainInf (stationaryPolicy M d (fun s => (hd s).1)) s) := by
  have hB : ∀ s, ∀ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j ≤ g + h s :=
    fun s => ((p016_residual_iff M g h s).1 (hres s)).1
  have hdeq : ∀ s, g + h s ≤ M.reward s (d s) + ∑ j, M.trans s (d s) j * h j := by
    intro s
    obtain ⟨a, ha, hae⟩ := ((p016_residual_iff M g h s).1 (hres s)).2
    rw [(hd s).2, ← hae]
    exact Finset.le_sup' (fun a => M.reward s a + ∑ j, M.trans s a j * h j) ha
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨fun _ s => (IsEmpty.false s).elim, fun s => (IsEmpty.false s).elim⟩
  obtain ⟨smin, hsmin⟩ := Finite.exists_min h
  obtain ⟨smax, hsmax⟩ := Finite.exists_max h
  constructor
  · intro π s
    apply p016_gainSup_le π s g (h s - h smin)
    intro N
    have := p016_tr_upper π g h (h smin) hsmin hB N 0 [] s
    linarith
  · intro s
    apply p016_le_gainInf _ s g (h smax - h s)
    intro N
    have := p016_tr_lower (stationaryPolicy M d (fun s => (hd s).1)) g h (h smax) hsmax
      (by
        intro t hist s' a ha hq
        have hads : a = d s' := by
          by_contra hne
          exact hq (by simp [stationaryPolicy, hne])
        subst hads; exact hdeq s') N 0 [] s
    linarith

open MarkovDecisionProcesses in
theorem community_optimality {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq A] (M : StationaryMDP S A) (hM : IsUnichain M) :
    (∃ (d : S → A) (hd : ∀ s, d s ∈ M.admissible s),
        IsAverageOptimal (stationaryPolicy M d hd)) ∧
    (∃ (gstar : ℝ) (hstar : S → ℝ), (∀ s, optimalityResidual M gstar hstar s = 0) ∧
        ∀ s, optGainSup M s = gstar ∧ optGainInf M s = gstar) ∧
    (∀ (gstar : ℝ) (hstar : S → ℝ), (∀ s, optimalityResidual M gstar hstar s = 0) →
        ∀ (d : S → A) (hd : IsImproving M hstar d),
          IsAverageOptimal (stationaryPolicy M d (fun s => (hd s).1))) := by
  have hc : ∀ (gstar : ℝ) (hstar : S → ℝ), (∀ s, optimalityResidual M gstar hstar s = 0) →
      ∀ (d : S → A) (hd : IsImproving M hstar d),
        IsAverageOptimal (stationaryPolicy M d (fun s => (hd s).1)) := by
    intro g h hres d hd π s
    obtain ⟨h1, h2⟩ := p016_bounds_of_improving g h hres d hd
    exact (h1 π s).trans (h2 s)
  obtain ⟨g, h, hB, hex⟩ := p016_exists_solution M hM
  have hres : ∀ s, optimalityResidual M g h s = 0 :=
    fun s => (p016_residual_iff M g h s).2 ⟨hB s, hex s⟩
  have himp : ∀ s, ∃ a ∈ M.admissible s, M.reward s a + ∑ j, M.trans s a j * h j =
      (M.admissible s).sup' (M.admissible_nonempty s)
        (fun a => M.reward s a + ∑ j, M.trans s a j * h j) := by
    intro s
    obtain ⟨a, ha, hae⟩ := Finset.exists_mem_eq_sup' (M.admissible_nonempty s)
      (fun a => M.reward s a + ∑ j, M.trans s a j * h j)
    exact ⟨a, ha, hae.symm⟩
  choose d hdadm hdeq using himp
  have hdimp : IsImproving M h d := fun s => ⟨hdadm s, hdeq s⟩
  obtain ⟨h1, h2⟩ := p016_bounds_of_improving g h hres d hdimp
  refine ⟨⟨d, fun s => (hdimp s).1, hc g h hres d hdimp⟩, ⟨g, h, hres, fun s => ?_⟩, hc⟩
  have hne : Nonempty (AvgHRPolicy M) := ⟨stationaryPolicy M d (fun s => (hdimp s).1)⟩
  have hbS : BddAbove (Set.range fun π : AvgHRPolicy M => gainSup π s) :=
    ⟨g, by rintro _ ⟨π, rfl⟩; exact h1 π s⟩
  have hbI : BddAbove (Set.range fun π : AvgHRPolicy M => gainInf π s) :=
    ⟨g, by rintro _ ⟨π, rfl⟩; exact (p016_inf_le_sup π s).trans (h1 π s)⟩
  unfold optGainSup optGainInf
  constructor
  · apply le_antisymm
    · exact ciSup_le (fun π => h1 π s)
    · calc g ≤ gainInf (stationaryPolicy M d (fun s => (hdimp s).1)) s := h2 s
        _ ≤ gainSup (stationaryPolicy M d (fun s => (hdimp s).1)) s := p016_inf_le_sup _ s
        _ ≤ ⨆ π : AvgHRPolicy M, gainSup π s := le_ciSup hbS _
  · apply le_antisymm
    · exact ciSup_le (fun π => (p016_inf_le_sup π s).trans (h1 π s))
    · exact (h2 s).trans (le_ciSup hbI _)

end

namespace Queelius.UnichainIteration
open MarkovDecisionProcesses PutermanMDP.Unichain
lemma evaluation_exists {S A : Type*} [Fintype S] [Fintype A]
    (M : StationaryMDP S A) (hM : IsUnichain M) (d : Rule M) :
    ∃ g h,Evaluates M d g h := by
  exact p016_poisson (P:=transMatrix M d.val) (fun i j => M.trans_nonneg i (d.val i) j) (fun i => M.trans_sum i (d.val i))
    (hM d.val d.property) (fun s => M.reward s (d.val s))
lemma improvement_exists {S A : Type*} [Fintype S] [Fintype A]
    (M : StationaryMDP S A) (d : Rule M) (h : S → ℝ) : ∃ d',Improves M d d' h := by
  classical
  by_cases hd : IsImproving M h d.val
  · exact ⟨d,hd,fun _ => rfl⟩
  · have he (s : S) : ∃ a ∈ M.admissible s,M.reward s a+∑ j,M.trans s a j*h j=
        (M.admissible s).sup' (M.admissible_nonempty s) (fun a => M.reward s a+∑ j,M.trans s a j*h j) := by
      obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_sup' (M.admissible_nonempty s)
        (fun a => M.reward s a+∑ j,M.trans s a j*h j)
      exact ⟨a,ha,he.symm⟩
    choose a ha heq using he
    exact ⟨⟨a,ha⟩,(fun s => ⟨ha s,heq s⟩),fun hbad => (hd hbad).elim⟩
lemma run_exists {S A : Type*} [Fintype S] [Fintype A]
    (M : StationaryMDP S A) (hM : IsUnichain M) (d₀ : Rule M) :
    ∃ (d : ℕ → Rule M) (g : ℕ → ℝ) (h : ℕ → S → ℝ),d 0=d₀ ∧ IsRun M d g h := by
  classical
  choose G H hev using evaluation_exists M hM
  choose D him using (fun d : Rule M => improvement_exists M d (H d))
  let d : ℕ → Rule M := fun n => D^[n] d₀
  refine ⟨d,fun n => G (d n),fun n => H (d n),rfl,fun n => hev _,?_⟩
  intro n
  change Improves M (D^[n] d₀) (D^[n+1] d₀) (H (D^[n] d₀))
  rw [Function.iterate_succ_apply']
  exact him _
lemma stopped_residual {S A : Type*} [Fintype S] [Fintype A]
    (M : StationaryMDP S A) (d : Rule M) (g : ℝ) (h : S → ℝ)
    (he : Evaluates M d g h) (hi : IsImproving M h d.val) :
    ∀ s,optimalityResidual M g h s=0 := by
  intro s
  apply (p016_residual_iff M g h s).mpr
  have hsup : (M.admissible s).sup' (M.admissible_nonempty s)
      (fun a => M.reward s a+∑ j,M.trans s a j*h j)=g+h s := by
    rw [← (hi s).2];exact (he s).symm
  refine ⟨?_,d.val s,d.property s,(he s).symm⟩
  intro a ha
  rw [← hsup]
  exact Finset.le_sup' (fun a => M.reward s a+∑ j,M.trans s a j*h j) ha
end Queelius.UnichainIteration

namespace Queelius.UnichainIteration
open MarkovDecisionProcesses PutermanMDP.Unichain
lemma stopped_optimality {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]
    (M : StationaryMDP S A) (d : Rule M) (g : ℝ) (h : S → ℝ)
    (he : Evaluates M d g h) (hi : IsImproving M h d.val) :
    (∀ s,optimalityResidual M g h s=0) ∧
      IsAverageOptimal (stationaryPolicy M d.val d.property) ∧
      (∀ s,optGainSup M s=g ∧ optGainInf M s=g) := by
  have hr := stopped_residual M d g h he hi
  obtain ⟨hupper,hlower⟩ := p016_bounds_of_improving g h hr d.val hi
  have hopt : IsAverageOptimal (stationaryPolicy M d.val d.property) := by
    intro π s
    exact (hupper π s).trans (hlower s)
  refine ⟨hr,hopt,?_⟩
  intro s
  have hne : Nonempty (AvgHRPolicy M) := ⟨stationaryPolicy M d.val d.property⟩
  have hbs : BddAbove (Set.range fun π : AvgHRPolicy M => gainSup π s) :=
    ⟨g,by rintro _ ⟨π,rfl⟩;exact hupper π s⟩
  have hbi : BddAbove (Set.range fun π : AvgHRPolicy M => gainInf π s) :=
    ⟨g,by rintro _ ⟨π,rfl⟩;exact (p016_inf_le_sup π s).trans (hupper π s)⟩
  unfold optGainSup optGainInf
  constructor
  · apply le_antisymm
    · exact ciSup_le (fun π => hupper π s)
    · exact (hlower s).trans ((p016_inf_le_sup _ s).trans (le_ciSup hbs (stationaryPolicy M d.val d.property)))
  · apply le_antisymm
    · exact ciSup_le (fun π => (p016_inf_le_sup π s).trans (hupper π s))
    · exact (hlower s).trans (le_ciSup hbi (stationaryPolicy M d.val d.property))
lemma run_stopped_conclusion {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]
    (M : StationaryMDP S A) (d : ℕ → Rule M) (g : ℕ → ℝ) (h : ℕ → S → ℝ)
    (hrun : IsRun M d g h) (n : ℕ) (hstop : StopsAt M d n) :
    (∀ s,optimalityResidual M (g n) (h n) s=0) ∧
      IsAverageOptimal (stationaryPolicy M (d n).val (d n).property) ∧
      (∀ s,optGainSup M s=g n ∧ optGainInf M s=g n) := by
  apply stopped_optimality M (d n) (g n) (h n) (hrun.1 n)
  have hi := (hrun.2 n).1
  simpa only [hstop.1] using hi
lemma least_stopping_index {S A : Type*} [Fintype S] [Fintype A]
    (M : StationaryMDP S A) (d : ℕ → Rule M)
    (hex : ∃ n,d (n+1)=d n) : ∃ n,StopsAt M d n := by
  classical
  exact ⟨Nat.find hex,Nat.find_spec hex,fun k hk => Nat.find_min hex hk⟩
end Queelius.UnichainIteration

open PutermanMDP.Unichain MarkovDecisionProcesses in
theorem prior_run_existence {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A] [Nonempty S]
    (M : StationaryMDP S A) (hM : IsUnichain M) (d₀ : Rule M) :
    ∃ (d : ℕ → Rule M) (g : ℕ → ℝ) (h : ℕ → S → ℝ),d 0=d₀ ∧ IsRun M d g h :=
  Queelius.UnichainIteration.run_exists M hM d₀

section
open Filter Topology Matrix


namespace BlackwellDiscreteDP.NearOne

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section MarkovTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

instance bmk_fc : FirstCountableTopology (Matrix n n ℝ) :=
  inferInstanceAs (FirstCountableTopology (n → n → ℝ))

lemma bmk_mul {A B : Matrix n n ℝ} (hA : IsMarkovMatrix A) (hB : IsMarkovMatrix B) :
    IsMarkovMatrix (A * B) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j)
  · simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hB.2, mul_one]
    exact hA.2 i

lemma bmk_one : IsMarkovMatrix (1 : Matrix n n ℝ) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [Matrix.one_apply]; split_ifs <;> norm_num
  · simp [Matrix.one_apply]

lemma bmk_pow {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (k : ℕ) : IsMarkovMatrix (P ^ k) := by
  induction k with
  | zero => simpa using (bmk_one (n := n))
  | succ k ih => rw [pow_succ]; exact bmk_mul ih hP

lemma bmk_le_one {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (i j : n) : P i j ≤ 1 := by
  rw [← hP.2 i]
  exact Finset.single_le_sum (f := fun j => P i j) (fun j _ => hP.1 i j) (Finset.mem_univ j)

lemma bmk_cesaro {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (N : ℕ) :
    IsMarkovMatrix (cesaroMean P N) := by
  unfold cesaroMean
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => (bmk_pow hP k).1 i j)
  · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [(bmk_pow hP _).2 i]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp

lemma bmk_P_mul_sum (P : Matrix n n ℝ) (N : ℕ) :
    P * ∑ k ∈ Finset.range (N + 1), P ^ k = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, ← pow_succ']
    abel

lemma bmk_sum_mul_P (P : Matrix n n ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), P ^ k) * P = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_mul, ih, ← pow_succ]
    abel

lemma bmk_P_cesaro (P : Matrix n n ℝ) (N : ℕ) :
    P * cesaroMean P N - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.mul_smul, bmk_P_mul_sum, smul_add]
  abel

lemma bmk_cesaro_P (P : Matrix n n ℝ) (N : ℕ) :
    cesaroMean P N * P - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.smul_mul, bmk_sum_mul_P, smul_add]
  abel

lemma bmk_D_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hb : ∀ N : ℕ, ‖(((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) i j‖ ≤ 1 / ((N : ℝ) + 1) := by
    intro N
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Real.norm_eq_abs]
    have h1 := (bmk_pow hP (N + 1)).1 i j
    have h2 := bmk_le_one (bmk_pow hP (N + 1)) i j
    have h3 : (0 : ℝ) ≤ (1 : Matrix n n ℝ) i j := bmk_one.1 i j
    have h4 : (1 : Matrix n n ℝ) i j ≤ 1 := bmk_le_one bmk_one i j
    rw [abs_mul, abs_of_pos (by positivity), one_div]
    have : |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc ((N : ℝ) + 1)⁻¹ * |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ ((N : ℝ) + 1)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  exact squeeze_zero_norm hb tendsto_one_div_add_atTop_nhds_zero_nat

lemma bmk_clus {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {L : Matrix n n ℝ}
    (hL : Tendsto (fun j => cesaroMean P (ns j)) atTop (𝓝 L)) : P * L = L ∧ L * P = L := by
  have hD := (bmk_D_tendsto hP).comp hns
  constructor
  · have h1 : Tendsto (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) atTop
        (𝓝 (P * L - L)) := (hL.const_mul P).sub hL
    have h2 : (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact bmk_P_cesaro P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)
  · have h1 : Tendsto (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) atTop
        (𝓝 (L * P - L)) := (hL.mul_const P).sub hL
    have h2 : (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact bmk_cesaro_P P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)

lemma bmk_avg_const (L : Matrix n n ℝ) (N : ℕ) :
    ((N : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (N + 1), L = L := by
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (by positivity), one_smul]

lemma bmk_cesaro_mul_fix {P L : Matrix n n ℝ} (h : P * L = L) (N : ℕ) :
    cesaroMean P N * L = L := by
  have hk : ∀ k : ℕ, P ^ k * L = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [hk]
  exact bmk_avg_const L N

lemma bmk_fix_mul_cesaro {P L : Matrix n n ℝ} (h : L * P = L) (N : ℕ) :
    L * cesaroMean P N = L := by
  have hk : ∀ k : ℕ, L * P ^ k = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.mul_smul, Finset.mul_sum]
  simp_rw [hk]
  exact bmk_avg_const L N

lemma bmk_compact : IsCompact {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} := by
  have e : {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} =
      Set.pi Set.univ (fun (_ : n) => Set.pi Set.univ (fun (_ : n) => Set.Icc (0 : ℝ) 1)) := by
    ext M; exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [e]
  exact isCompact_univ_pi (fun (_ : n) => isCompact_univ_pi (fun (_ : n) => isCompact_Icc))

theorem bmk_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (cesaroMean P) atTop (𝓝 (limitMatrix P)) := by
  have hmem : ∀ N, cesaroMean P N ∈ {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} :=
    fun N i j => ⟨(bmk_cesaro hP N).1 i j, bmk_le_one (bmk_cesaro hP N) i j⟩
  obtain ⟨L, -, φ, hφ, hL⟩ := bmk_compact.tendsto_subseq hmem
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨hPL, hLP⟩ := bmk_clus hP hφt hL
  have main : Tendsto (cesaroMean P) atTop (𝓝 L) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨L', -, ψ, hψ, hL'⟩ := bmk_compact.tendsto_subseq (fun j => hmem (ns j))
    refine ⟨ψ, ?_⟩
    have hnsψ : Tendsto (ns ∘ ψ) atTop atTop := hns.comp hψ.tendsto_atTop
    obtain ⟨hPL', hL'P⟩ := bmk_clus hP hnsψ hL'
    have e1 : L * L' = L' := by
      have t : Tendsto (fun j => cesaroMean P (φ j) * L') atTop (𝓝 (L * L')) := hL.mul_const L'
      simp_rw [bmk_cesaro_mul_fix hPL'] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have e2 : L * L' = L := by
      have t : Tendsto (fun j => L * cesaroMean P ((ns ∘ ψ) j)) atTop (𝓝 (L * L')) :=
        hL'.const_mul L
      simp_rw [bmk_fix_mul_cesaro hLP] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have : L' = L := e1.symm.trans e2
    rw [this] at hL'
    exact hL'
  rw [limitMatrix, main.limUnder_eq]
  exact main

variable {P : Matrix n n ℝ}

lemma bmk_PL (hP : IsMarkovMatrix P) : P * limitMatrix P = limitMatrix P :=
  (bmk_clus hP tendsto_id (bmk_tendsto hP)).1

lemma bmk_LP (hP : IsMarkovMatrix P) : limitMatrix P * P = limitMatrix P :=
  (bmk_clus hP tendsto_id (bmk_tendsto hP)).2

lemma bmk_LL (hP : IsMarkovMatrix P) : limitMatrix P * limitMatrix P = limitMatrix P := by
  have t : Tendsto (fun N => cesaroMean P N * limitMatrix P) atTop
      (𝓝 (limitMatrix P * limitMatrix P)) := (bmk_tendsto hP).mul_const _
  simp_rw [bmk_cesaro_mul_fix (bmk_PL hP)] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma bmk_fixvec (hP : IsMarkovMatrix P) {v : n → ℝ} (hv : P *ᵥ v = v) :
    limitMatrix P *ᵥ v = v := by
  have hk : ∀ k : ℕ, (P ^ k) *ᵥ v = v := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  have hA : ∀ N, cesaroMean P N *ᵥ v = v := by
    intro N
    rw [cesaroMean, Matrix.smul_mulVec, Matrix.sum_mulVec]
    simp_rw [hk]
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by positivity), one_smul]
  have t : Tendsto (fun N => cesaroMean P N *ᵥ v) atTop (𝓝 (limitMatrix P *ᵥ v)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp (bmk_tendsto hP)
  simp_rw [hA] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma bmk_L_markov (hP : IsMarkovMatrix P) : IsMarkovMatrix (limitMatrix P) := by
  have hc : IsClosed {M : Matrix n n ℝ | IsMarkovMatrix M} := by
    have : {M : Matrix n n ℝ | IsMarkovMatrix M} =
        (⋂ i, ⋂ j, {M : Matrix n n ℝ | 0 ≤ M i j}) ∩ ⋂ i, {M : Matrix n n ℝ | ∑ j, M i j = 1} := by
      ext M; simp [IsMarkovMatrix]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
      (isClosed_iInter fun i => ?_)
    · exact isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
    · exact isClosed_eq (continuous_finsetSum _ fun j _ =>
        (continuous_apply j).comp (continuous_apply i)) continuous_const
  exact hc.mem_of_tendsto (bmk_tendsto hP) (Eventually.of_forall fun N => bmk_cesaro hP N)

lemma bmk_ZL_inj (hP : IsMarkovMatrix P) :
    Function.Injective (1 - P + limitMatrix P).mulVec := by
  set L := limitMatrix P
  have hLA : L * (1 - P + L) = L := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
  intro v w hvw
  set d := v - w
  have hd : (1 - P + L) *ᵥ d = 0 := by
    simp only [d, Matrix.mulVec_sub, hvw, sub_self]
  have hLd : L *ᵥ d = 0 := by
    have := congrArg (fun z => L *ᵥ z) hd
    simp only [Matrix.mulVec_mulVec, hLA, Matrix.mulVec_zero] at this
    exact this
  have hPd : P *ᵥ d = d := by
    have := hd
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, hLd, Matrix.one_mulVec, add_zero, sub_eq_zero] at this
    exact this.symm
  have : d = 0 := by rw [← bmk_fixvec hP hPd, hLd]
  exact sub_eq_zero.1 this

lemma bmk_Z_unit (hP : IsMarkovMatrix P) : IsUnit (1 - P + limitMatrix P).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_injective_iff_isUnit.1 (bmk_ZL_inj hP))

lemma bmk_PH (hP : IsMarkovMatrix P) :
    P * deviationMatrix P = deviationMatrix P + limitMatrix P - 1 := by
  set L := limitMatrix P
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + L) * (1 - P + L)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hLZ : L * (1 - P + L)⁻¹ = L := by
    have hLA : L * (1 - P + L) = L := by
      rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
    calc L * (1 - P + L)⁻¹ = (L * (1 - P + L)) * (1 - P + L)⁻¹ := by rw [hLA]
      _ = L * ((1 - P + L) * (1 - P + L)⁻¹) := Matrix.mul_assoc _ _ _
      _ = L := by rw [h1, Matrix.mul_one]
  have h2 : (1 - P + L) * (1 - P + L)⁻¹ = (1 - P + L)⁻¹ - P * (1 - P + L)⁻¹ + L * (1 - P + L)⁻¹ := by
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul]
  rw [h1, hLZ] at h2
  unfold deviationMatrix
  rw [Matrix.mul_sub, bmk_PL hP]
  change P * (1 - P + L)⁻¹ - L = (1 - P + L)⁻¹ - L + L - 1
  generalize (1 - P + L)⁻¹ = Z at h2 ⊢
  have : P * Z = Z + L - 1 := by rw [h2]; abel
  rw [this]; abel

lemma bmk_LH (hP : IsMarkovMatrix P) : limitMatrix P * deviationMatrix P = 0 := by
  set L := limitMatrix P
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + L) * (1 - P + L)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hLA : L * (1 - P + L) = L := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
  have hLZ : L * (1 - P + L)⁻¹ = L := by
    calc L * (1 - P + L)⁻¹ = (L * (1 - P + L)) * (1 - P + L)⁻¹ := by rw [hLA]
      _ = L * ((1 - P + L) * (1 - P + L)⁻¹) := Matrix.mul_assoc _ _ _
      _ = L := by rw [h1, Matrix.mul_one]
  unfold deviationMatrix
  rw [Matrix.mul_sub, hLZ, bmk_LL hP, sub_self]

/-- maximum principle: if `w = c + β P w` and `c ≤ K` then `w ≤ K/(1-β)` -/
lemma bmk_upper (hP : IsMarkovMatrix P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w c : n → ℝ}
    (hw : ∀ s, w s = c s + β * (P *ᵥ w) s) {K : ℝ} (hc : ∀ s, c s ≤ K) [Nonempty n] (s : n) :
    w s ≤ K / (1 - β) := by
  obtain ⟨s0, hs0⟩ := Finite.exists_max w
  have hPw : (P *ᵥ w) s0 ≤ w s0 := by
    show ∑ j, P s0 j * w j ≤ w s0
    calc ∑ j, P s0 j * w j ≤ ∑ j, P s0 j * w s0 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hs0 j) (hP.1 s0 j)
      _ = w s0 := by rw [← Finset.sum_mul, hP.2 s0, one_mul]
  have h1 := hw s0
  have h2 : (1 - β) * w s0 ≤ K := by nlinarith [hc s0]
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hs0 s]

lemma bmk_lower (hP : IsMarkovMatrix P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w c : n → ℝ}
    (hw : ∀ s, w s = c s + β * (P *ᵥ w) s) {K : ℝ} (hc : ∀ s, K ≤ c s) [Nonempty n] (s : n) :
    K / (1 - β) ≤ w s := by
  have := bmk_upper hP hβ0 hβ1 (w := -w) (c := -c) (K := -K)
    (fun s => by simp only [Pi.neg_apply, Matrix.mulVec_neg]; rw [hw s]; ring)
    (fun s => by simp only [Pi.neg_apply]; linarith [hc s]) s
  simp only [Pi.neg_apply, neg_div] at this
  linarith

lemma bmk_abs (hP : IsMarkovMatrix P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w c : n → ℝ}
    (hw : ∀ s, w s = c s + β * (P *ᵥ w) s) {K : ℝ} (hc : ∀ s, |c s| ≤ K) [Nonempty n] (s : n) :
    |w s| ≤ K / (1 - β) := by
  rw [abs_le]
  constructor
  · have := bmk_lower hP hβ0 hβ1 hw (K := -K) (fun s => (abs_le.1 (hc s)).1) s
    rw [neg_div] at this; exact this
  · exact bmk_upper hP hβ0 hβ1 hw (fun s => (abs_le.1 (hc s)).2) s

theorem lemma_1b_core [Nonempty n] (Q : Matrix n n ℝ) (hQ : IsMarkovMatrix Q) :
    (1 - Q).rank + (limitMatrix Q).rank = Fintype.card n := by
  have hker : LinearMap.ker (1 - Q).mulVecLin = LinearMap.range (limitMatrix Q).mulVecLin := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · intro h
      refine ⟨v, bmk_fixvec hQ ?_⟩
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
      exact h.symm
    · rintro ⟨w, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, bmk_PL hQ, sub_self,
        Matrix.zero_mulVec]
  unfold Matrix.rank
  rw [← hker, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

end MarkovTheory

end BlackwellDiscreteDP.NearOne

open BlackwellDiscreteDP.NearOne


theorem prior_blackwell_rank {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (Q : Matrix n n ℝ) (hQ : IsMarkovMatrix Q) :
    (1 - Q).rank + (limitMatrix Q).rank = Fintype.card n := by
  exact lemma_1b_core Q hQ

end

namespace Queelius.UnichainIteration
open MarkovDecisionProcesses PutermanMDP.Unichain Matrix Finset
lemma residual_nonneg {S A : Type*} [Fintype S] [Fintype A]
    (M : StationaryMDP S A) (d : Rule M) (g : ℝ) (h : S → ℝ) (he : Evaluates M d g h) :
    ∀ s,0 ≤ optimalityResidual M g h s := by
  intro s
  have hb := Finset.le_sup' (fun a => M.reward s a-g+∑ j,M.trans s a j*h j-h s) (d.property s)
  have hz : M.reward s (d.val s)-g+∑ j,M.trans s (d.val s) j*h j-h s=0 := by linarith [he s]
  rw [hz] at hb
  exact hb
lemma residual_improving {S A : Type*} [Fintype S] [Fintype A]
    (M : StationaryMDP S A) (d : Rule M) (g : ℝ) (h : S → ℝ) (hi : IsImproving M h d.val) :
    ∀ s,optimalityResidual M g h s=M.reward s (d.val s)-g+∑ j,M.trans s (d.val s) j*h j-h s := by
  intro s
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    have hb := Finset.le_sup' (fun a => M.reward s a+∑ j,M.trans s a j*h j) ha
    rw [← (hi s).2] at hb
    linarith
  · exact Finset.le_sup' (fun a => M.reward s a-g+∑ j,M.trans s a j*h j-h s) (hi s).1
lemma evaluation_difference {S A : Type*} [Fintype S] [Fintype A]
    (M : StationaryMDP S A) (d d' : Rule M) (g g' : ℝ) (h h' : S → ℝ)
    (he : Evaluates M d g h) (he' : Evaluates M d' g' h') (hi : IsImproving M h d'.val) :
    ∀ s,(g'-g)+(h' s-h s)=optimalityResidual M g h s+
      ∑ j,transMatrix M d'.val s j*(h' j-h j) := by
  intro s
  rw [residual_improving M d' g h hi s]
  simp only [transMatrix,mul_sub,Finset.sum_sub_distrib]
  linarith [he' s]
lemma limit_gain_identity {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (hP : BlackwellDiscreteDP.NearOne.IsMarkovMatrix P)
    (c : ℝ) (u v : S → ℝ) (he : ∀ s,c+u s=v s+∑ j,P s j*u j) :
    ∀ s,c=(BlackwellDiscreteDP.NearOne.limitMatrix P *ᵥ v) s := by
  let L := BlackwellDiscreteDP.NearOne.limitMatrix P
  have hL := BlackwellDiscreteDP.NearOne.bmk_L_markov hP
  have hc : L *ᵥ (fun _ : S => c)=(fun _ : S => c) := by
    funext s
    change (∑ j,L s j*c)=c
    rw [← Finset.sum_mul,hL.2 s,one_mul]
  have hv : (fun _ : S => c)+u=v+P *ᵥ u := funext he
  have hm := congrArg (fun w => L *ᵥ w) hv
  rw [Matrix.mulVec_add,Matrix.mulVec_add,hc,Matrix.mulVec_mulVec,
    BlackwellDiscreteDP.NearOne.bmk_LP hP] at hm
  intro s
  have hs := congrFun hm s
  simp only [Pi.add_apply] at hs
  linarith
lemma gain_nonnegative {S : Type*} [Fintype S] [Nonempty S]
    (P : S → S → ℝ) (hP0 : ∀ i j,0 ≤ P i j) (hP1 : ∀ i,∑ j,P i j=1)
    (c : ℝ) (u v : S → ℝ) (hv : ∀ i,0 ≤ v i)
    (he : ∀ i,c+u i=v i+∑ j,P i j*u j) : 0 ≤ c := by
  obtain ⟨i,hi⟩ := Finite.exists_min u
  have hb := p016_avg_ge_min hP0 hP1 hi
  linarith [he i,hv i]
lemma gain_strict_recurrent {S : Type*} [Fintype S] [Nonempty S]
    (P : S → S → ℝ) (hP0 : ∀ i j,0 ≤ P i j) (hP1 : ∀ i,∑ j,P i j=1)
    (hU : IsUnichainMatrix P) (c : ℝ) (u v : S → ℝ) (hv : ∀ i,0 ≤ v i)
    (he : ∀ i,c+u i=v i+∑ j,P i j*u j)
    (hstrict : ∃ s,IsRecurrent P s ∧ 0 < v s) : 0 < c := by
  have hc := gain_nonnegative P hP0 hP1 c u v hv he
  by_contra hn
  have hc0 : c=0 := by linarith
  obtain ⟨i,hi⟩ := Finite.exists_min u
  have hclosed : ∀ a b,u a=u i → 0 < P a b → u b=u i := by
    intro a b ha hab
    have hmin : ∀ k,u a ≤ u k := by intro k;rw [ha];exact hi k
    have heq := p016_min_principle hP0 hP1 hmin (by have := he a;rw [hc0] at this;linarith [hv a]) b hab
    exact heq.trans ha
  obtain ⟨s,hs,hvpos⟩ := hstrict
  have hsi := p016_closed_mem_recurrent hU hclosed rfl hs
  have hb := p016_avg_ge hP0 hP1 s hi
  have heq := he s
  rw [hc0,hsi] at heq
  linarith
lemma recurrent_successor {S : Type*} (P : S → S → ℝ) {i j : S}
    (hi : IsRecurrent P i) (hij : 0 < P i j) : IsRecurrent P j := by
  intro k hjk
  have hstep : Accessible P i j := Relation.ReflTransGen.single hij
  exact (hi k (hstep.trans hjk)).trans hstep
lemma average_support_lower {S : Type*} [Fintype S] (p u : S → ℝ)
    (hp0 : ∀ j,0 ≤ p j) (hp1 : ∑ j,p j=1) (a : ℝ)
    (hb : ∀ j,0 < p j → a ≤ u j) : a ≤ ∑ j,p j*u j := by
  calc
    a = ∑ j,p j*a := by rw [← Finset.sum_mul,hp1,one_mul]
    _ ≤ ∑ j,p j*u j := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hz : p j=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hb j (lt_of_le_of_ne (hp0 j) (Ne.symm hz))) (hp0 j)
lemma zero_recurrent_gain {S : Type*} [Fintype S] [Nonempty S]
    (P : S → S → ℝ) (hP0 : ∀ i j,0 ≤ P i j) (hP1 : ∀ i,∑ j,P i j=1)
    (c : ℝ) (u v : S → ℝ) (hz : ∀ s,IsRecurrent P s → v s=0)
    (he : ∀ i,c+u i=v i+∑ j,P i j*u j) : c=0 := by
  classical
  let R := {s : S // IsRecurrent P s}
  letI : Fintype R := Fintype.ofFinite _
  have hR : Nonempty R := by
    obtain ⟨s⟩ := ‹Nonempty S›
    obtain ⟨r,_,hr⟩ := p016_exists_recurrent P s
    exact ⟨⟨r,hr⟩⟩
  obtain ⟨a,ha⟩ := Finite.exists_min (fun s : R => u s.val)
  obtain ⟨b,hb⟩ := Finite.exists_max (fun s : R => u s.val)
  have hlow : u a.val ≤ ∑ j,P a.val j*u j :=
    average_support_lower _ u (hP0 a.val) (hP1 a.val) _
      (fun j hj => ha ⟨j,recurrent_successor P a.property hj⟩)
  have hupp : -u b.val ≤ ∑ j,P b.val j*(-u j) :=
    average_support_lower _ (fun j => -u j) (hP0 b.val) (hP1 b.val) _
      (fun j hj => by have hh := hb ⟨j,recurrent_successor P b.property hj⟩;linarith)
  have hea := he a.val
  have heb := he b.val
  rw [hz a.val a.property] at hea
  rw [hz b.val b.property] at heb
  simp only [mul_neg,Finset.sum_neg_distrib] at hupp
  linarith
end Queelius.UnichainIteration

open MarkovDecisionProcesses PutermanMDP.Unichain Matrix in
theorem prior_gain_update {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [Nonempty S]
    (M : StationaryMDP S A) (hM : IsUnichain M)
    (d d' : Rule M) (g g' : ℝ) (h h' : S → ℝ)
    (heval : Evaluates M d g h) (heval' : Evaluates M d' g' h')
    (himp : IsImproving M h d'.val) :
    (∀ s,g'=g+(policyLimit M d').mulVec (optimalityResidual M g h) s) ∧
    ((∃ s,IsRecurrent (transMatrix M d'.val) s ∧ 0 < optimalityResidual M g h s) → g < g') ∧
    ((∀ s,IsRecurrent (transMatrix M d'.val) s → optimalityResidual M g h s=0) → g'=g) := by
  let P := transMatrix M d'.val
  let u : S → ℝ := h'-h
  let v : S → ℝ := optimalityResidual M g h
  have hP0 : ∀ i j,0 ≤ P i j := fun i j => M.trans_nonneg i (d'.val i) j
  have hP1 : ∀ i,∑ j,P i j=1 := fun i => M.trans_sum i (d'.val i)
  have hP : BlackwellDiscreteDP.NearOne.IsMarkovMatrix P := ⟨hP0,hP1⟩
  have he : ∀ s,(g'-g)+u s=v s+∑ j,P s j*u j :=
    Queelius.UnichainIteration.evaluation_difference M d d' g g' h h' heval heval' himp
  have hv : ∀ s,0 ≤ v s := Queelius.UnichainIteration.residual_nonneg M d g h heval
  refine ⟨?_,?_,?_⟩
  · intro s
    have hi := Queelius.UnichainIteration.limit_gain_identity P hP (g'-g) u v he s
    change g'=g+(BlackwellDiscreteDP.NearOne.limitMatrix P *ᵥ v) s
    linarith
  · intro hs
    have hc := Queelius.UnichainIteration.gain_strict_recurrent P hP0 hP1
      (hM d'.val d'.property) (g'-g) u v hv he hs
    linarith
  · intro hz
    have hc := Queelius.UnichainIteration.zero_recurrent_gain P hP0 hP1 (g'-g) u v hz he
    linarith

namespace Queelius.UnichainIteration
open MarkovDecisionProcesses PutermanMDP.Unichain Matrix Finset
open BlackwellDiscreteDP.NearOne
lemma markov_constant {S : Type*} [Fintype S] (P : Matrix S S ℝ)
    (hP1 : ∀ i,∑ j,P i j=1) (c : ℝ) : P *ᵥ (fun _ => c)=(fun _ => c) := by
  funext i
  change (∑ j,P i j*c)=c
  rw [← Finset.sum_mul,hP1 i,one_mul]
lemma deviation_right {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (hP : IsMarkovMatrix P) :
    deviationMatrix P*(1-P)=1-limitMatrix P := by
  let L := limitMatrix P
  let A := 1-P+L
  have hu : IsUnit A.det := bmk_Z_unit hP
  have hZA : A⁻¹*A=1 := Matrix.nonsing_inv_mul A hu
  have hAL : A*L=L := by
    dsimp [A,L]
    rw [Matrix.add_mul,Matrix.sub_mul,Matrix.one_mul,bmk_PL hP,bmk_LL hP];abel
  have hLA : L*A=L := by
    dsimp [A,L]
    rw [Matrix.mul_add,Matrix.mul_sub,Matrix.mul_one,bmk_LP hP,bmk_LL hP];abel
  have hZL : A⁻¹*L=L := by
    calc
      A⁻¹*L=A⁻¹*(A*L) := by rw [hAL]
      _ = (A⁻¹*A)*L := (Matrix.mul_assoc _ _ _).symm
      _ = L := by rw [hZA,Matrix.one_mul]
  have hIP : 1-P=A-L := by dsimp [A];abel
  change (A⁻¹-L)*(1-P)=1-L
  rw [hIP,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,hZA,hZL,hLA]
  have hLL : L*L=L := bmk_LL hP
  rw [hLL];abel
lemma deviation_constant {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (hP : IsMarkovMatrix P) (c : ℝ) :
    deviationMatrix P *ᵥ (fun _ => c)=0 := by
  let L := limitMatrix P
  let A := 1-P+L
  have hu : IsUnit A.det := bmk_Z_unit hP
  have hZA : A⁻¹*A=1 := Matrix.nonsing_inv_mul A hu
  have hLc : L *ᵥ (fun _ => c)=(fun _ => c) := markov_constant L (bmk_L_markov hP).2 c
  have hAc : A *ᵥ (fun _ => c)=(fun _ => c) := by
    dsimp [A]
    rw [Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,markov_constant P hP.2 c,hLc]
    simp
  have hZc : A⁻¹ *ᵥ (fun _ => c)=(fun _ => c) := by
    calc
      A⁻¹ *ᵥ (fun _ => c)=A⁻¹ *ᵥ (A *ᵥ (fun _ => c)) := by rw [hAc]
      _ = (fun _ => c) := by rw [Matrix.mulVec_mulVec,hZA,Matrix.one_mulVec]
  change (A⁻¹-L) *ᵥ (fun _ => c)=0
  rw [Matrix.sub_mulVec,hZc,hLc,sub_self]
lemma deviation_poisson {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (hP : IsMarkovMatrix P) (g : ℝ) (h r : S → ℝ)
    (he : ∀ i,g+h i=r i+∑ j,P i j*h j) :
    deviationMatrix P *ᵥ r=h-limitMatrix P *ᵥ h := by
  have hr : r=(fun _ => g)+(1-P) *ᵥ h := by
    funext i
    simp only [Pi.add_apply,Matrix.sub_mulVec,Matrix.one_mulVec,Pi.sub_apply]
    change r i=g+(h i-∑ j,P i j*h j)
    linarith [he i]
  rw [hr,Matrix.mulVec_add,deviation_constant P hP,zero_add,Matrix.mulVec_mulVec,
    deviation_right P hP,Matrix.sub_mulVec,Matrix.one_mulVec]
lemma harmonic_constant {S : Type*} [Fintype S] [Nonempty S]
    (P : S → S → ℝ) (hP0 : ∀ i j,0 ≤ P i j) (hP1 : ∀ i,∑ j,P i j=1)
    (hU : IsUnichainMatrix P) (u : S → ℝ) (he : ∀ i,u i=∑ j,P i j*u j) :
    ∃ c,∀ i,u i=c := by
  obtain ⟨a,ha⟩ := Finite.exists_min u
  obtain ⟨b,hb⟩ := Finite.exists_max u
  have hmin : ∀ i j,u i=u a → 0 < P i j → u j=u a := by
    intro i j hi hij
    have hh := p016_min_principle hP0 hP1 (u:=u) (s:=i) (fun k => by rw [hi];exact ha k) (by rw [← he i]) j hij
    exact hh.trans hi
  have hmax : ∀ i j,u i=u b → 0 < P i j → u j=u b := by
    intro i j hi hij
    have hh := p016_min_principle hP0 hP1 (u:=fun k => -u k)
      (fun k => by rw [hi];exact neg_le_neg (hb k))
      (by simp only [mul_neg,Finset.sum_neg_distrib];rw [← he i]) j hij
    have hji : u j=u i := neg_injective hh
    exact hji.trans hi
  obtain ⟨r,_,hr⟩ := p016_exists_recurrent P a
  have h1 := p016_closed_mem_recurrent hU hmin rfl hr
  have h2 := p016_closed_mem_recurrent hU hmax rfl hr
  refine ⟨u a,fun i => ?_⟩
  exact le_antisymm (by have := hb i;linarith) (ha i)
end Queelius.UnichainIteration
open MarkovDecisionProcesses PutermanMDP.Unichain Matrix in
open BlackwellDiscreteDP.NearOne in
theorem prior_bias_update {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [Nonempty S]
    (M : StationaryMDP S A) (hM : IsUnichain M) (d d' : Rule M) (g : ℝ) (h : S → ℝ)
    (heval : Evaluates M d g h) (himp : Improves M d d' h) :
    policyBias M d'=policyBias M d-(policyLimit M d').mulVec (policyBias M d)+
      (policyDeviation M d').mulVec (optimalityResidual M g h) := by
  let P : Matrix S S ℝ := transMatrix M d.val
  let P' : Matrix S S ℝ := transMatrix M d'.val
  have hP : IsMarkovMatrix P := ⟨fun i j => M.trans_nonneg i (d.val i) j,fun i => M.trans_sum i (d.val i)⟩
  have hP' : IsMarkovMatrix P' := ⟨fun i j => M.trans_nonneg i (d'.val i) j,fun i => M.trans_sum i (d'.val i)⟩
  have hold : policyBias M d=h-limitMatrix P *ᵥ h :=
    Queelius.UnichainIteration.deviation_poisson P hP g h (policyReward M d) heval
  have hfix : ∀ i,(limitMatrix P *ᵥ h) i=∑ j,P i j*(limitMatrix P *ᵥ h) j := by
    have hh : P *ᵥ (limitMatrix P *ᵥ h)=limitMatrix P *ᵥ h := by rw [Matrix.mulVec_mulVec,bmk_PL hP]
    intro i;exact (congrFun hh i).symm
  obtain ⟨c,hc⟩ := Queelius.UnichainIteration.harmonic_constant P hP.1 hP.2 (hM d.val d.property) _ hfix
  have hLc : limitMatrix P *ᵥ h=(fun _ => c) := funext hc
  rw [hLc] at hold
  have hr : policyReward M d'=(fun _ => g)+(1-P') *ᵥ h+optimalityResidual M g h := by
    funext i
    have hh := Queelius.UnichainIteration.residual_improving M d' g h himp.1 i
    simp only [Pi.add_apply,Matrix.sub_mulVec,Matrix.one_mulVec,Pi.sub_apply]
    change M.reward i (d'.val i)=g+(h i-∑ j,P' i j*h j)+optimalityResidual M g h i
    change optimalityResidual M g h i=M.reward i (d'.val i)-g+∑ j,P' i j*h j-h i at hh
    linarith
  have hnew : policyBias M d'=h-limitMatrix P' *ᵥ h+
      deviationMatrix P' *ᵥ optimalityResidual M g h := by
    change deviationMatrix P' *ᵥ policyReward M d'=_
    rw [hr,Matrix.mulVec_add,Matrix.mulVec_add,Queelius.UnichainIteration.deviation_constant P' hP',zero_add,
      Matrix.mulVec_mulVec,Queelius.UnichainIteration.deviation_right P' hP',Matrix.sub_mulVec,Matrix.one_mulVec]
  change policyBias M d'=policyBias M d-limitMatrix P' *ᵥ policyBias M d+
    deviationMatrix P' *ᵥ optimalityResidual M g h
  rw [hnew,hold,Matrix.mulVec_sub,Queelius.UnichainIteration.markov_constant (limitMatrix P') (bmk_L_markov hP').2 c]
  ext i
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

namespace Queelius.UnichainTransient
open MarkovDecisionProcesses PutermanMDP.Unichain Matrix Finset
open BlackwellDiscreteDP.NearOne Queelius.UnichainIteration

lemma sum_transient {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (f : S → ℝ) (hf : ∀ i,IsRecurrent P i → f i=0) :
    ∑ i,f i=∑ i : TransientStates P,f i.val := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => ¬IsRecurrent P i) f
  have hz : ∑ i : {s // ¬¬IsRecurrent P s}, f i.val=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hf i.val (not_not.mp i.property)
  rw [hz,add_zero] at h
  exact h.symm.trans (Finset.sum_congr (by ext i; simp) (fun i hi => rfl))

lemma recurrent_no_exit {S : Type*} (P : Matrix S S ℝ) (hP0 : ∀ i j,0 ≤ P i j)
    {i j : S} (hi : IsRecurrent P i) (hj : ¬IsRecurrent P j) : P i j=0 := by
  by_contra hn
  exact hj (recurrent_successor P hi (lt_of_le_of_ne (hP0 i j) (Ne.symm hn)))

lemma harmonic_zero {S : Type*} [Fintype S] [Nonempty S]
    (P : S → S → ℝ) (hP0 : ∀ i j,0 ≤ P i j) (hP1 : ∀ i,∑ j,P i j=1)
    (hU : IsUnichainMatrix P) (u : S → ℝ)
    (he : ∀ i,u i=∑ j,P i j*u j) (hz : ∀ i,IsRecurrent P i → u i=0) : u=0 := by
  obtain ⟨c,hc⟩ := harmonic_constant P hP0 hP1 hU u he
  obtain ⟨i⟩ := ‹Nonempty S›
  obtain ⟨r,_,hr⟩ := p016_exists_recurrent P i
  have hc0 : c=0 := (hc r).symm.trans (hz r hr)
  funext s
  exact (hc s).trans hc0

noncomputable def extendTransient {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (v : TransientStates P → ℝ) (i : S) : ℝ := by
  classical
  exact if h : ¬IsRecurrent P i then v ⟨i,h⟩ else 0

lemma transient_kernel {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsMarkovMatrix P) (hU : IsUnichainMatrix P)
    (v : TransientStates P → ℝ) (hv : (1-transientBlock P P) *ᵥ v=0) : v=0 := by
  classical
  let u := extendTransient P v
  have hz : ∀ i,IsRecurrent P i → u i=0 := by
    intro i hi
    simp [u,extendTransient,hi]
  have ht : ∀ i : TransientStates P,u i.val=v i := by
    intro i
    simp [u,extendTransient,i.property]
  have he : ∀ i,u i=∑ j,P i j*u j := by
    intro i
    by_cases hi : IsRecurrent P i
    · rw [hz i hi]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hr : IsRecurrent P j
      · rw [hz j hr,mul_zero]
      · rw [recurrent_no_exit P hP.1 hi hr,zero_mul]
    · have hh := congrFun hv ⟨i,hi⟩
      rw [Matrix.sub_mulVec,Matrix.one_mulVec] at hh
      change v ⟨i,hi⟩-(∑ j : TransientStates P,P i j.val*v j)=0 at hh
      rw [sum_transient P (fun j => P i j*u j) (fun j hj => by rw [hz j hj,mul_zero])]
      simp_rw [ht]
      rw [show u i=v ⟨i,hi⟩ from ht ⟨i,hi⟩]
      exact sub_eq_zero.mp hh
  have hu := harmonic_zero P hP.1 hP.2 hU u he hz
  funext i
  rw [← ht i,hu]
  rfl

lemma transient_unit {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsMarkovMatrix P) (hU : IsUnichainMatrix P) :
    IsUnit (1-transientBlock P P).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hd : (1-transientBlock P P) *ᵥ (v-w)=0 := by rw [Matrix.mulVec_sub,hvw,sub_self]
  exact sub_eq_zero.mp (transient_kernel P hP hU (v-w) hd)

lemma limit_transient_zero {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsMarkovMatrix P) (hU : IsUnichainMatrix P)
    (i j : S) (hj : ¬IsRecurrent P j) : limitMatrix P i j=0 := by
  classical
  let B : Matrix (TransientStates P) (TransientStates P) ℝ := 1-transientBlock P P
  let v : TransientStates P → ℝ := fun k => limitMatrix P i k.val
  have hb : IsUnit B := (Matrix.isUnit_iff_isUnit_det _).mpr (transient_unit P hP hU)
  have hv : v ᵥ* B=0 := by
    funext k
    rw [show B=1-transientBlock P P from rfl,Matrix.vecMul_sub,Matrix.vecMul_one]
    change v k-(∑ l : TransientStates P,v l*P l.val k.val)=0
    have he := congrArg (fun Q : Matrix S S ℝ => Q i k.val) (bmk_LP hP)
    change (∑ l,limitMatrix P i l*P l k.val)=limitMatrix P i k.val at he
    rw [sum_transient P (fun l => limitMatrix P i l*P l k.val)
      (fun l hl => by rw [recurrent_no_exit P hP.1 hl k.property,mul_zero])] at he
    exact sub_eq_zero.mpr he.symm
  have hz : v=0 := (Matrix.vecMul_injective_iff_isUnit.mpr hb) (by simpa using hv)
  exact congrFun hz ⟨j,hj⟩

lemma deviation_transient_row {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsMarkovMatrix P) (hU : IsUnichainMatrix P) (i : S) :
    (fun j : TransientStates P => deviationMatrix P i j.val) ᵥ*
      (1-transientBlock P P)=(fun j : TransientStates P => (1 : Matrix S S ℝ) i j.val) := by
  classical
  funext j
  rw [Matrix.vecMul_sub,Matrix.vecMul_one]
  change deviationMatrix P i j.val-(∑ k : TransientStates P,deviationMatrix P i k.val*P k.val j.val)=(1 : Matrix S S ℝ) i j.val
  have he := congrArg (fun Q : Matrix S S ℝ => Q i j.val) (deviation_right P hP)
  rw [Matrix.mul_sub,Matrix.mul_one] at he
  change deviationMatrix P i j.val-(∑ k,deviationMatrix P i k*P k j.val)=
    (1 : Matrix S S ℝ) i j.val-limitMatrix P i j.val at he
  rw [limit_transient_zero P hP hU i j.val j.property,sub_zero] at he
  rw [sum_transient P (fun k => deviationMatrix P i k*P k j.val)
    (fun k hk => by rw [recurrent_no_exit P hP.1 hk j.property,mul_zero])] at he
  exact he

lemma deviation_RT {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsMarkovMatrix P) (hU : IsUnichainMatrix P)
    (i j : S) (hi : IsRecurrent P i) (hj : ¬IsRecurrent P j) : deviationMatrix P i j=0 := by
  classical
  have hu : IsUnit (1-transientBlock P P) := (Matrix.isUnit_iff_isUnit_det _).mpr (transient_unit P hP hU)
  have he := deviation_transient_row P hP hU i
  have hh : (fun k : TransientStates P => (1 : Matrix S S ℝ) i k.val)=0 := by
    funext k
    have hne : i ≠ k.val := by intro h;exact k.property (h ▸ hi)
    simp [Matrix.one_apply,hne]
  rw [hh] at he
  have hz : (fun k : TransientStates P => deviationMatrix P i k.val)=0 :=
    (Matrix.vecMul_injective_iff_isUnit.mpr hu) (by simpa using he)
  exact congrFun hz ⟨j,hj⟩

lemma deviation_TT {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsMarkovMatrix P) (hU : IsUnichainMatrix P) :
    transientBlock P (deviationMatrix P)=transientResolvent P := by
  classical
  let B : Matrix (TransientStates P) (TransientStates P) ℝ := 1-transientBlock P P
  have hu : IsUnit B.det := transient_unit P hP hU
  have he : transientBlock P (deviationMatrix P)*B=1 := by
    ext i j
    have hh := congrFun (deviation_transient_row P hP hU i.val) j
    change (∑ k : TransientStates P,deviationMatrix P i.val k.val*B k j)=_ at hh
    change (∑ k : TransientStates P,deviationMatrix P i.val k.val*B k j)=_
    convert hh using 1
    simp only [Matrix.one_apply]
    simp only [Subtype.ext_iff]
  change transientBlock P (deviationMatrix P)=B⁻¹
  calc
    transientBlock P (deviationMatrix P)=transientBlock P (deviationMatrix P)*(B*B⁻¹) := by rw [Matrix.mul_nonsing_inv B hu,Matrix.mul_one]
    _ = (transientBlock P (deviationMatrix P)*B)*B⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = B⁻¹ := by rw [he,Matrix.one_mul]

lemma superharmonic_nonneg {S : Type*} [Fintype S] [Nonempty S]
    (P : S → S → ℝ) (hP0 : ∀ i j,0 ≤ P i j) (hP1 : ∀ i,∑ j,P i j=1)
    (hU : IsUnichainMatrix P) (v : S → ℝ)
    (hz : ∀ i,IsRecurrent P i → v i=0)
    (hle : ∀ i,∑ j,P i j*v j ≤ v i) : ∀ i,0 ≤ v i := by
  obtain ⟨a,ha⟩ := Finite.exists_min v
  have hc : ∀ i j,v i=v a → 0 < P i j → v j=v a := by
    intro i j hi hij
    exact (p016_min_principle hP0 hP1 (u:=v) (s:=i) (fun k => by rw [hi];exact ha k) (hle i) j hij).trans hi
  obtain ⟨r,_,hr⟩ := p016_exists_recurrent P a
  have hmin := p016_closed_mem_recurrent hU hc rfl hr
  have ha0 : v a=0 := hmin.symm.trans (hz r hr)
  intro i
  rw [← ha0]
  exact ha i

lemma deviation_nonnegative_support {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsMarkovMatrix P) (hU : IsUnichainMatrix P) (u : S → ℝ)
    (hz : ∀ i,IsRecurrent P i → u i=0)
    (hn : ∀ i,¬IsRecurrent P i → 0 ≤ u i) :
    ∀ i,u i ≤ (deviationMatrix P *ᵥ u) i ∧ 0 ≤ u i := by
  classical
  let v := deviationMatrix P *ᵥ u
  have hu0 : ∀ i,0 ≤ u i := by
    intro i
    by_cases hi : IsRecurrent P i
    · rw [hz i hi]
    · exact hn i hi
  have hvR : ∀ i,IsRecurrent P i → v i=0 := by
    intro i hi
    change (∑ j,deviationMatrix P i j*u j)=0
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hr : IsRecurrent P j
    · rw [hz j hr,mul_zero]
    · rw [deviation_RT P hP hU i j hi hr,zero_mul]
  have hLu : limitMatrix P *ᵥ u=0 := by
    funext i
    change (∑ j,limitMatrix P i j*u j)=0
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hr : IsRecurrent P j
    · rw [hz j hr,mul_zero]
    · rw [limit_transient_zero P hP hU i j hr,zero_mul]
  have hleft : (1-P)*deviationMatrix P=1-limitMatrix P := by
    rw [Matrix.sub_mul,Matrix.one_mul,bmk_PH hP]
    abel
  have he : v-P *ᵥ v=u := by
    have hx : (1-P) *ᵥ v=u := by
      dsimp only [v]
      rw [Matrix.mulVec_mulVec,hleft,Matrix.sub_mulVec,Matrix.one_mulVec,hLu,sub_zero]
    simpa only [Matrix.sub_mulVec,Matrix.one_mulVec] using hx
  have hle : ∀ i,∑ j,P i j*v j ≤ v i := by
    intro i
    have hh := congrFun he i
    change v i-(∑ j,P i j*v j)=u i at hh
    linarith [hu0 i]
  have hv0 := superharmonic_nonneg P hP.1 hP.2 hU v hvR hle
  intro i
  refine ⟨?_,hu0 i⟩
  have hp0 : 0 ≤ ∑ j,P i j*v j := Finset.sum_nonneg (fun j hj => mul_nonneg (hP.1 i j) (hv0 j))
  have hh := congrFun he i
  change v i-(∑ j,P i j*v j)=u i at hh
  change u i ≤ v i
  linarith
end Queelius.UnichainTransient


namespace PutermanMDP.Unichain

open MarkovDecisionProcesses Matrix in
/-- Lemma 8.6.4: all three clauses, including the full transient inverse. -/
theorem _root_.solution {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [Nonempty S] (M : StationaryMDP S A) (d : Rule M)
    (hd : IsUnichainMatrix (transMatrix M d.val)) :
    (∀ i j, IsRecurrent (transMatrix M d.val) i →
      ¬ IsRecurrent (transMatrix M d.val) j → policyDeviation M d i j = 0) ∧
    (transientBlock (transMatrix M d.val) (policyDeviation M d) =
      transientResolvent (transMatrix M d.val)) ∧
    (∀ u : S → ℝ,
      (∀ s, IsRecurrent (transMatrix M d.val) s → u s = 0) →
      (∀ s, ¬ IsRecurrent (transMatrix M d.val) s → 0 ≤ u s) →
      ∀ s, u s ≤ (policyDeviation M d).mulVec u s ∧ 0 ≤ u s) := by
  let P : Matrix S S ℝ := transMatrix M d.val
  have hP : BlackwellDiscreteDP.NearOne.IsMarkovMatrix P :=
    ⟨fun i j => M.trans_nonneg i (d.val i) j,fun i => M.trans_sum i (d.val i)⟩
  exact ⟨Queelius.UnichainTransient.deviation_RT P hP hd,
    Queelius.UnichainTransient.deviation_TT P hP hd,
    Queelius.UnichainTransient.deviation_nonnegative_support P hP hd⟩

end PutermanMDP.Unichain
