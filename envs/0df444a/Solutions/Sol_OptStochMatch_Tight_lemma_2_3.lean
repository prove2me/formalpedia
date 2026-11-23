-- Prove2me | solution 1 for OptStochMatch.Tight.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:37:51.296832+00:00
-- url     : https://prove2.me/submissions/35fe9445-c9d0-4b06-adbe-3bfec8642b9e

import Definitions.Def_OptStochMatch_Tight_Basic

namespace AuxLemma23

open Set OptStochMatch.Tight
open scoped NNReal BigOperators RealInnerProductSpace

def FeasibleFlow {m : ℕ} (lam : Ty m → ℝ≥0) (f : Ty m → Fin m → ℝ) : Prop :=
  (∀ S i, 0 ≤ f S i) ∧ (∀ S i, i ∉ S → f S i = 0) ∧ ∀ S, ∑ i, f S i ≤ (lam S : ℝ)

noncomputable def aggFlow {m : ℕ} (f : Ty m → Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ S, f S i

lemma feasibleFlow_coord_le {m : ℕ} {lam : Ty m → ℝ≥0} {f : Ty m → Fin m → ℝ}
    (hf : FeasibleFlow lam f) (S : Ty m) (i : Fin m) : f S i ≤ (lam S : ℝ) :=
  (Finset.single_le_sum (fun j _ => hf.1 S j) (Finset.mem_univ i)).trans (hf.2.2 S)

lemma aggFlow_mem_Plam {m : ℕ} {lam : Ty m → ℝ≥0} {f : Ty m → Fin m → ℝ}
    (hf : FeasibleFlow lam f) : aggFlow f ∈ Plam lam := by
  refine ⟨fun i => Finset.sum_nonneg fun S _ => hf.1 S i, fun A => ?_⟩
  unfold aggFlow coverRate
  rw [Finset.sum_comm]
  calc
    ∑ S : Ty m, ∑ i ∈ A, f S i
      ≤ ∑ S : Ty m, if (S ∩ A).Nonempty then (lam S : ℝ) else 0 := by
        refine Finset.sum_le_sum fun S _ => ?_
        by_cases hA : (S ∩ A).Nonempty
        · rw [if_pos hA]
          exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
            (fun i _ _ => hf.1 S i)).trans (hf.2.2 S)
        · rw [if_neg hA]
          exact le_of_eq (Finset.sum_eq_zero fun i hiA =>
            hf.2.1 S i fun hiS => hA ⟨i, Finset.mem_inter.mpr ⟨hiS, hiA⟩⟩)
    _ = ∑ S ∈ (Finset.univ.filter fun S : Ty m => (S ∩ A).Nonempty), (lam S : ℝ) := by
        rw [Finset.sum_filter]

def flowSet {m : ℕ} (lam : Ty m → ℝ≥0) : Set (Ty m → Fin m → ℝ) :=
  {f | FeasibleFlow lam f}

lemma zero_mem_flowSet {m : ℕ} (lam : Ty m → ℝ≥0) : (0 : Ty m → Fin m → ℝ) ∈ flowSet lam :=
  ⟨fun _ _ => le_rfl, fun _ _ _ => rfl, fun S => by simp⟩

lemma flowSet_compact {m : ℕ} (lam : Ty m → ℝ≥0) : IsCompact (flowSet lam) := by
  have h0 : IsClosed {f : Ty m → Fin m → ℝ | ∀ S i, 0 ≤ f S i} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun S => isClosed_iInter fun i =>
      isClosed_le continuous_const ((continuous_apply i).comp (continuous_apply S))
  have hs : IsClosed {f : Ty m → Fin m → ℝ | ∀ S i, i ∉ S → f S i = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun S => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply i).comp (continuous_apply S)) continuous_const
  have hc : IsClosed {f : Ty m → Fin m → ℝ | ∀ S, ∑ i, f S i ≤ (lam S : ℝ)} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun S => isClosed_le
      (continuous_finset_sum _ fun i _ => (continuous_apply i).comp (continuous_apply S))
      continuous_const
  refine (isCompact_Icc : IsCompact (Icc (0 : Ty m → Fin m → ℝ) (fun S _ => (lam S : ℝ)))).of_isClosed_subset
    (h0.inter (hs.inter hc)) ?_
  intro f hf
  exact ⟨hf.1, fun S i => feasibleFlow_coord_le hf S i⟩

lemma flowSet_convex {m : ℕ} (lam : Ty m → ℝ≥0) : Convex ℝ (flowSet lam) := by
  intro f hf g hg a b ha hb hab
  refine ⟨fun S i => add_nonneg (mul_nonneg ha (hf.1 S i)) (mul_nonneg hb (hg.1 S i)), ?_, ?_⟩
  · intro S i hi
    change a * f S i + b * g S i = 0
    rw [hf.2.1 S i hi, hg.2.1 S i hi]; ring
  · intro S
    change ∑ i, (a * f S i + b * g S i) ≤ (lam S : ℝ)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      a * ∑ i, f S i + b * ∑ i, g S i
        ≤ a * (lam S : ℝ) + b * (lam S : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left (hf.2.2 S) ha)
            (mul_le_mul_of_nonneg_left (hg.2.2 S) hb)
      _ = (lam S : ℝ) := by rw [← add_mul, hab, one_mul]

lemma exists_supporting_flow {m : ℕ} (lam : Ty m → ℝ≥0) (x : Fin m → ℝ) :
    ∃ f : Ty m → Fin m → ℝ, FeasibleFlow lam f ∧
      ∀ g, FeasibleFlow lam g →
        ∑ i, (x i - aggFlow f i) * (aggFlow g i - aggFlow f i) ≤ 0 := by
  let Φ : (Ty m → Fin m → ℝ) → ℝ := fun f => ∑ i, (x i - aggFlow f i) ^ 2
  have hΦ_cont : Continuous Φ := by
    refine continuous_finset_sum _ fun i _ => ?_
    refine Continuous.pow ?_ 2
    exact continuous_const.sub (continuous_finset_sum _ fun S _ =>
      (continuous_apply i).comp (continuous_apply S))
  obtain ⟨f, hf, hmin⟩ := (flowSet_compact lam).exists_isMinOn ⟨0, zero_mem_flowSet lam⟩ hΦ_cont.continuousOn
  refine ⟨f, hf, fun g hg => ?_⟩
  by_contra hpos'
  have hpos : 0 < ∑ i, (x i - aggFlow f i) * (aggFlow g i - aggFlow f i) := lt_of_not_ge hpos'
  let A : ℝ := ∑ i, (x i - aggFlow f i) * (aggFlow g i - aggFlow f i)
  let B : ℝ := ∑ i, (aggFlow g i - aggFlow f i) ^ 2
  have hB_nn : 0 ≤ B := Finset.sum_nonneg fun i _ => sq_nonneg _
  let t : ℝ := min (1 / 2) (A / (B + 1))
  have ht_pos : 0 < t := lt_min (by norm_num) (div_pos hpos (by linarith))
  have ht_le1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hcomb : (1 - t) • f + t • g ∈ flowSet lam :=
    flowSet_convex lam hf hg (by linarith) (le_of_lt ht_pos) (by ring)
  have hagg_comb : ∀ i, aggFlow ((1 - t) • f + t • g) i =
      aggFlow f i + t * (aggFlow g i - aggFlow f i) := by
    intro i
    unfold aggFlow
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hlin : ∀ S : Ty m, (1 - t) * f S i + t * g S i = f S i + t * (g S i - f S i) :=
      fun S => by ring
    simp_rw [hlin, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hdiff : Φ ((1 - t) • f + t • g) - Φ f = -2 * t * A + t ^ 2 * B := by
    dsimp [Φ, A, B]
    simp_rw [hagg_comb]
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ i, (x i - (aggFlow f i + t * (aggFlow g i - aggFlow f i))) ^ 2 -
        (x i - aggFlow f i) ^ 2 =
        (-2 * t) * ((x i - aggFlow f i) * (aggFlow g i - aggFlow f i)) +
          t ^ 2 * (aggFlow g i - aggFlow f i) ^ 2 := fun i => by ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hge : Φ f ≤ Φ ((1 - t) • f + t • g) := hmin hcomb
  have htB : t * B < 2 * A := by
    have hle : t ≤ A / (B + 1) := min_le_right _ _
    have hmul : t * (B + 1) ≤ A := (le_div_iff₀ (by linarith)).mp hle
    nlinarith
  nlinarith

lemma weighted_sum_update {m : ℕ} (v r : Fin m → ℝ) (i : Fin m) (a : ℝ) :
    ∑ j, r j * Function.update v i a j = (∑ j, r j * v j) + r i * (a - v i) := by
  have he : (fun j => r j * Function.update v i a j) =
      fun j => r j * v j + if j = i then r i * (a - v i) else 0 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp; ring
    · simp [hj]
  rw [he, Finset.sum_add_distrib]
  simp

lemma sum_update_val {m : ℕ} (v : Fin m → ℝ) (i : Fin m) (a : ℝ) :
    ∑ j, Function.update v i a j = (∑ j, v j) + (a - v i) := by
  simpa only [one_mul] using weighted_sum_update v (fun _ => 1) i a

lemma supporting_row_opt {m : ℕ} {lam : Ty m → ℝ≥0} {x : Fin m → ℝ} {f : Ty m → Fin m → ℝ}
    (hf : FeasibleFlow lam f)
    (hs : ∀ g, FeasibleFlow lam g → ∑ i, (x i - aggFlow f i) * (aggFlow g i - aggFlow f i) ≤ 0)
    (S : Ty m) (v : Fin m → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hvs : ∀ i, i ∉ S → v i = 0)
    (hvc : ∑ i, v i ≤ (lam S : ℝ)) :
    ∑ i, (x i - aggFlow f i) * v i ≤ ∑ i, (x i - aggFlow f i) * f S i := by
  have hupd : FeasibleFlow lam (Function.update f S v) := by
    refine ⟨fun T i => ?_, fun T i hi => ?_, fun T => ?_⟩
    · by_cases hT : T = S
      · subst hT; simpa using hv0 i
      · simpa [hT] using hf.1 T i
    · by_cases hT : T = S
      · subst hT; simpa using hvs i hi
      · simpa [hT] using hf.2.1 T i hi
    · by_cases hT : T = S
      · subst hT; simpa using hvc
      · simpa [hT] using hf.2.2 T
  have hagg : ∀ i, aggFlow (Function.update f S v) i = aggFlow f i + (v i - f S i) := by
    intro i
    have he : (fun T => Function.update f S v T i) = Function.update (fun T => f T i) S (v i) := by
      funext T; by_cases hT : T = S <;> simp [hT]
    unfold aggFlow
    rw [he]
    have hmem : S ∈ (Finset.univ : Finset (Ty m)) := Finset.mem_univ S
    rw [← Finset.add_sum_erase _ _ hmem]
    have herase : ∑ T ∈ (Finset.univ : Finset (Ty m)).erase S, Function.update (fun T => f T i) S (v i) T =
        ∑ T ∈ (Finset.univ : Finset (Ty m)).erase S, f T i :=
      Finset.sum_congr rfl fun T hT => by simp [(Finset.mem_erase.mp hT).1]
    have horig := Finset.add_sum_erase (Finset.univ : Finset (Ty m)) (fun T => f T i) hmem
    rw [herase]; simp; linarith
  have h := hs (Function.update f S v) hupd
  simp_rw [hagg, add_sub_cancel_left, mul_sub] at h
  rw [Finset.sum_sub_distrib] at h
  linarith

lemma supporting_flow_dominates {m : ℕ} {lam : Ty m → ℝ≥0} {x : Fin m → ℝ} {f : Ty m → Fin m → ℝ}
    (hx : x ∈ Plam lam) (hf : FeasibleFlow lam f)
    (hs : ∀ g, FeasibleFlow lam g → ∑ i, (x i - aggFlow f i) * (aggFlow g i - aggFlow f i) ≤ 0) :
    ∀ i, x i ≤ aggFlow f i := by
  let A : Finset (Fin m) := Finset.univ.filter fun i => 0 < x i - aggFlow f i
  have hpos : ∀ i ∈ A, 0 < x i - aggFlow f i := fun i hi => (Finset.mem_filter.mp hi).2
  have hnonpos : ∀ i, i ∉ A → x i - aggFlow f i ≤ 0 := by
    intro i hi; by_contra h; exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩)
  have hrow : ∀ S : Ty m, ∑ i ∈ A, f S i = if (S ∩ A).Nonempty then (lam S : ℝ) else 0 := by
    intro S
    by_cases ht : (S ∩ A).Nonempty
    · rw [if_pos ht]
      obtain ⟨i, hi⟩ := ht
      obtain ⟨hiS, hiA⟩ := Finset.mem_inter.mp hi
      have hpos_i := hpos i hiA
      have hzero_out : ∀ j, j ∉ A → f S j = 0 := by
        intro j hjA
        have hneg_j := hnonpos j hjA
        have hij : i ≠ j := fun he => by subst he; linarith
        let v := Function.update (Function.update (f S) j 0) i (f S i + f S j)
        have hv0 : ∀ k, 0 ≤ v k := by
          intro k
          by_cases hki : k = i
          · subst hki; simpa [v] using add_nonneg (hf.1 S k) (hf.1 S j)
          · by_cases hkj : k = j
            · subst hkj; simp [v, hki]
            · simpa [v, hki, hkj] using hf.1 S k
        have hvs : ∀ k, k ∉ S → v k = 0 := by
          intro k hk
          have hki : k ≠ i := fun he => hk (he ▸ hiS)
          by_cases hkj : k = j
          · subst hkj; simp [v, hki]
          · simpa [v, hki, hkj] using hf.2.1 S k hk
        have hvc : ∑ k, v k ≤ (lam S : ℝ) := by
          rw [sum_update_val, sum_update_val, Function.update_of_ne hij]
          linarith [hf.2.2 S]
        have hm := supporting_row_opt hf hs S v hv0 hvs hvc
        rw [weighted_sum_update, weighted_sum_update, Function.update_of_ne hij] at hm
        nlinarith [hf.1 S j]
      have hsum_A : ∑ j ∈ A, f S j = ∑ j, f S j := by
        refine Finset.sum_subset (Finset.subset_univ A) fun j _ hj => hzero_out j hj
      rw [hsum_A]
      let δ := (lam S : ℝ) - ∑ j, f S j
      have hδ : 0 ≤ δ := sub_nonneg.mpr (hf.2.2 S)
      let v := Function.update (f S) i (f S i + δ)
      have hv0 : ∀ j, 0 ≤ v j := by
        intro j
        by_cases hj : j = i
        · subst hj; simpa [v] using add_nonneg (hf.1 S j) hδ
        · simpa [v, hj] using hf.1 S j
      have hvs : ∀ j, j ∉ S → v j = 0 := by
        intro j hj
        have hji : j ≠ i := fun he => hj (he ▸ hiS)
        simpa [v, hji] using hf.2.1 S j hj
      have hvc : ∑ j, v j ≤ (lam S : ℝ) := by
        rw [sum_update_val]; dsimp [δ]; linarith
      have hm := supporting_row_opt hf hs S v hv0 hvs hvc
      rw [weighted_sum_update] at hm
      have hd : δ = 0 := by nlinarith
      dsimp [δ] at hd; linarith
    · rw [if_neg ht]
      exact Finset.sum_eq_zero fun i hiA =>
        hf.2.1 S i fun hiS => ht ⟨i, Finset.mem_inter.mpr ⟨hiS, hiA⟩⟩
  have hcut : ∑ i ∈ A, aggFlow f i = coverRate lam A := by
    unfold aggFlow coverRate
    rw [Finset.sum_comm, Finset.sum_filter]
    exact Finset.sum_congr rfl fun S _ => hrow S
  have hA : A = ∅ := by
    by_contra hne
    have hlt : ∑ i ∈ A, aggFlow f i < ∑ i ∈ A, x i :=
      Finset.sum_lt_sum_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hne)
        fun i hi => sub_pos.mp (hpos i hi)
    rw [hcut] at hlt
    exact not_lt_of_ge (hx.2 A) hlt
  intro i
  have h := hnonpos i (by simp [hA])
  linarith

end AuxLemma23

open scoped NNReal BigOperators
open OptStochMatch.Tight AuxLemma23

theorem solution {m : ℕ} (lam : Ty m → ℝ≥0) (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i) :
    x ∈ Plam lam ↔
      ∃ F : Fin m → Ty m → ℝ, (∀ i S, 0 ≤ F i S) ∧
        (∀ S : Ty m, ∑ i ∈ S, F i S ≤ (lam S : ℝ)) ∧
        ∀ i : Fin m, ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), F i S = x i := by
  constructor
  · intro hxP
    obtain ⟨f, hf, hs⟩ := exists_supporting_flow lam x
    have hle := supporting_flow_dominates hxP hf hs
    let q : Fin m → ℝ := fun i => x i / aggFlow f i
    have hw : ∀ i, 0 ≤ aggFlow f i := fun i => Finset.sum_nonneg fun S _ => hf.1 S i
    have hq0 : ∀ i, 0 ≤ q i := fun i => div_nonneg (hx i) (hw i)
    have hq1 : ∀ i, q i ≤ 1 := by
      intro i
      by_cases hi : aggFlow f i = 0
      · simp [q, hi]
      · exact (div_le_one (lt_of_le_of_ne (hw i) (Ne.symm hi))).mpr (hle i)
    refine ⟨fun i S => f S i * q i, ?_, ?_, ?_⟩
    · exact fun i S => mul_nonneg (hf.1 S i) (hq0 i)
    · intro S
      calc
        ∑ i ∈ S, f S i * q i
          ≤ ∑ i : Fin m, f S i * q i :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
              fun i _ _ => mul_nonneg (hf.1 S i) (hq0 i)
        _ ≤ ∑ i : Fin m, f S i :=
            Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hf.1 S i) (hq1 i)
        _ ≤ (lam S : ℝ) := hf.2.2 S
    · intro i
      have hsupp : ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), f S i * q i =
          ∑ S : Ty m, f S i * q i := by
        refine Finset.sum_subset (Finset.subset_univ _) fun S _ hS => ?_
        have hiS : i ∉ S := fun hiS => hS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS⟩)
        rw [hf.2.1 S i hiS, zero_mul]
      rw [hsupp, ← Finset.sum_mul]
      change aggFlow f i * (x i / aggFlow f i) = x i
      by_cases hi : aggFlow f i = 0
      · have hxi : x i = 0 := le_antisymm (by simpa [hi] using hle i) (hx i)
        simp [hi, hxi]
      · field_simp
  · rintro ⟨F, hF_nn, hF_cap, hF_sum⟩
    let f : Ty m → Fin m → ℝ := fun S i => if i ∈ S then F i S else 0
    have hf : FeasibleFlow lam f := by
      refine ⟨fun S i => by dsimp [f]; split_ifs; exacts [hF_nn i S, le_rfl],
        fun S i hi => by simp [f, hi], fun S => ?_⟩
      have hS : ∑ i : Fin m, f S i = ∑ i ∈ S, F i S := by
        dsimp [f]
        rw [← Finset.sum_filter]
        have heq : Finset.univ.filter (fun i : Fin m => i ∈ S) = S := by ext i; simp
        rw [heq]
      rw [hS]
      exact hF_cap S
    have hagg : aggFlow f = x := by
      funext i
      unfold aggFlow
      dsimp [f]
      rw [← Finset.sum_filter, hF_sum i]
    rw [← hagg]
    exact aggFlow_mem_Plam hf
