-- Prove2me | solution 1 for Puder.tendsto_card_primitivityRank_eq_rpow_of_sqrt_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T20:34:05.682321+00:00
-- url     : https://prove2.me/submissions/ca766e3c-5d07-4132-9aa7-d40f0657be06

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Theorems.Thm_Puder_tendsto_card_reduced_primitivityRank_eq_rpow_of_sqrt_lt
import Theorems.Thm_Puder_exists_eventually_cogrowth_pow_le_sum
import Theorems.Thm_Puder_limsup_sum_ncard_crit_rpow_le_rhoStair
import Theorems.Thm_Puder_isAlgExt_zpowers_of_mem_crit
import Theorems.Thm_Puder_setOf_isAlgExt_finite_of_fg

namespace Puder.Q284Fin

/-- `Crit(w)` is finite: critical subgroups are algebraic extensions of `⟨w⟩` (Claim 3.1), of which there are
finitely many (Takahasi). -/
theorem crit_finite {d : ℕ} (w : FreeGroup (Fin d)) : (Puder.Crit w).Finite :=
  (Puder.setOf_isAlgExt_finite_of_fg (Subgroup.zpowers w)
      ⟨{w}, by rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure]⟩).subset
    fun _ hJ => Puder.isAlgExt_zpowers_of_mem_crit hJ

end Puder.Q284Fin


/-! q263: Puder Theorem 8.5 in the case `2m - 1 > √(2k-1)`, from Theorem 8.2 (reduced words),
the lower cogrowth bound, Corollary 4.5 and Theorem 2.3 (finiteness of `Crit`).
The upper bound and the reduced-word bridge are copied from q218 (`Q218PartY`, `Q218PartX`,
`Q218PartA`). -/

open Filter Topology

namespace Puder.Q263T85L

/-- The endpoint of the walk spelled by a letter sequence. -/
noncomputable def word {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) : FreeGroup (Fin k) :=
  StrongConv.wordFree (List.ofFn fun j => some (i j))

/-- `b_{k,m}(t)`: the number of words of length `t` with primitivity rank `m`. -/
noncomputable def b (k m t : ℕ) : ℝ :=
  ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k => primitivityRank (word i) = m).card : ℝ)

theorem b_nonneg (k m t : ℕ) : 0 ≤ b k m t := by unfold b; positivity

theorem crit_nonempty {k : ℕ} (w : FreeGroup (Fin k)) (m : ℕ) (h : primitivityRank w = m) :
    (Crit w).Nonempty := by
  classical
  have hex : ∃ r : ℕ, ∃ J : Subgroup (FreeGroup (Fin k)), w ∈ J ∧ HasRank J r ∧
      ¬ IsPrimitiveIn J w := by
    by_contra hne
    push Not at hne
    have htop : primitivityRank w = ⊤ := by
      unfold primitivityRank
      simp only [iInf_eq_top]
      intro r hr
      obtain ⟨J, h1, h2, h3⟩ := hr
      exact absurd h3 (not_not.mpr (hne r J h1 h2))
    rw [htop] at h
    exact ENat.top_ne_natCast m h
  have hval : primitivityRank w = (Nat.find hex : ℕ∞) := by
    unfold primitivityRank
    apply le_antisymm
    · exact iInf₂_le (Nat.find hex) (Nat.find_spec hex)
    · exact le_iInf₂ fun r hr => by exact_mod_cast Nat.find_min' hex hr
  obtain ⟨J, hw, hr, hnp⟩ := Nat.find_spec hex
  exact ⟨J, hw, hnp, Nat.find hex, hr, hval.symm⟩

/-! ## Upper bound -/

theorem upper (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ => b k m t ^ (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ => b k m t ^ (1 / (t : ℝ))) atTop ≤ StrongConv.rhoStair k m := by
  obtain ⟨hB, hL⟩ := Puder.limsup_sum_ncard_crit_rpow_le_rhoStair k m hk hm1 hm
  have hle : ∀ t : ℕ, b k m t ^ (1 / (t : ℝ)) ≤
      (∑ i : Fin t → Fin k ⊕ Fin k with
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ)) := by
    intro t
    apply Real.rpow_le_rpow (b_nonneg k m t) _ (by positivity)
    unfold b
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_filter] at hi
    have hne := crit_nonempty _ m hi.2
    have := (Set.ncard_pos (Puder.Q284Fin.crit_finite _)).2 hne
    simp only [Nat.cast_one]
    exact_mod_cast this
  have hB' : IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ => b k m t ^ (1 / (t : ℝ))) :=
    hB.mono_le (Eventually.of_forall hle)
  refine ⟨hB', le_trans (limsup_le_limsup (Eventually.of_forall hle) ?_ hB) hL⟩
  exact isCoboundedUnder_le_of_le atTop (fun t => Real.rpow_nonneg (b_nonneg k m t) _)

/-! ## Non-backtracking sequences are the reduced ones -/

/-- The generator a letter stands for. -/
def gen {k : ℕ} : Fin k ⊕ Fin k → FreeGroup (Fin k)
  | Sum.inl x => FreeGroup.of x
  | Sum.inr x => (FreeGroup.of x)⁻¹

/-- The letter as a generator-with-sign pair. -/
def toP {k : ℕ} : Fin k ⊕ Fin k → Fin k × Bool
  | Sum.inl x => (x, true)
  | Sum.inr x => (x, false)

theorem word_eq {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    word i = (List.ofFn fun j => gen (i j)).prod := by
  unfold word StrongConv.wordFree
  rw [List.map_ofFn]
  congr 2
  funext j
  simp only [Function.comp]
  rcases i j with x | x <;> rfl

theorem gen_eq_mk {k : ℕ} (a : Fin k ⊕ Fin k) : gen a = FreeGroup.mk [toP a] := by
  rcases a with x | x
  · rfl
  · simp [gen, toP, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]

theorem prod_map_gen {k : ℕ} (l : List (Fin k ⊕ Fin k)) :
    (l.map gen).prod = FreeGroup.mk (l.map toP) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, gen_eq_mk, FreeGroup.mul_mk]
    rfl

theorem word_eq_mk {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    word i = FreeGroup.mk (List.ofFn fun j => toP (i j)) := by
  rw [word_eq]
  have h1 : (List.ofFn fun j => gen (i j)) = (List.ofFn i).map gen := by
    rw [List.map_ofFn]; rfl
  have h2 : (List.ofFn fun j => toP (i j)) = (List.ofFn i).map toP := by
    rw [List.map_ofFn]; rfl
  rw [h1, h2, prod_map_gen]

theorem toP_rel {k : ℕ} (a b : Fin k ⊕ Fin k) :
    ((toP a).1 = (toP b).1 → (toP a).2 = (toP b).2) ↔ b ≠ a.swap := by
  rcases a with x | x <;> rcases b with y | y <;> simp [toP, eq_comm]

theorem NB_iff_isReduced {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    (∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap) ↔
      FreeGroup.IsReduced (List.ofFn fun j => toP (i j)) := by
  rw [FreeGroup.IsReduced, List.isChain_ofFn]
  simp only [toP_rel]
  constructor
  · intro H j hj
    exact H ⟨j, by omega⟩ hj
  · intro H j hj
    exact H j hj

theorem NB_iff_length {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    (∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap) ↔
      (word i).toWord.length = t := by
  rw [NB_iff_isReduced, word_eq_mk, FreeGroup.toWord_mk]
  set M := List.ofFn fun j => toP (i j)
  have hM : M.length = t := by simp [M]
  constructor
  · intro hr
    rw [hr.reduce_eq, hM]
  · intro hl
    by_contra hr
    rw [FreeGroup.isReduced_iff_not_step] at hr
    push Not at hr
    obtain ⟨L₂, hs⟩ := hr
    have e := FreeGroup.reduce.Step.eq hs
    have hle := FreeGroup.Red.length_le (FreeGroup.reduce.red (L := L₂))
    have hst := hs.length
    rw [e] at hl
    omega

/-! ## Lower bound -/

open Classical in
/-- The indicator of primitivity rank `m`. -/
noncomputable def ind {k : ℕ} (m : ℕ) (g : FreeGroup (Fin k)) : ℝ :=
  if primitivityRank g = m then 1 else 0

theorem lower (k m : ℕ) (hk : 2 ≤ k) (hm : m ≤ k) (hlt : Real.sqrt (2 * k - 1) < 2 * m - 1)
    (α : ℝ) (hα1 : Real.sqrt (2 * k - 1) < α) (hα2 : α < 2 * m - 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℕ in atTop, C * ((2 * k - 1) / α + α) ^ t ≤ b k m t := by
  classical
  have hα0 : 0 ≤ α := le_trans (Real.sqrt_nonneg _) hα1.le
  have hT := Puder.tendsto_card_reduced_primitivityRank_eq_rpow_of_sqrt_lt k m hk hm hlt
  have hev := hT.eventually (eventually_gt_nhds hα2)
  have hν : ∀ᶠ t : ℕ in atTop, 1 * α ^ t ≤ ∑ i : Fin t → Fin k ⊕ Fin k with
      (∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap),
      ind m (StrongConv.wordFree (List.ofFn fun j => some (i j))) := by
    filter_upwards [hev, eventually_ge_atTop 1] with t h1 ht
    set c : ℝ := ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m).card : ℝ)
      with hc
    have hsum : (∑ i : Fin t → Fin k ⊕ Fin k with
        (∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap),
        ind m (StrongConv.wordFree (List.ofFn fun j => some (i j)))) = c := by
      unfold ind
      rw [Finset.sum_boole, Finset.filter_filter, hc]
      congr 2
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [NB_iff_length]
      rfl
    rw [hsum, one_mul]
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have hpow : α ^ t ≤ (c ^ (1 / (t : ℝ))) ^ t := pow_le_pow_left₀ hα0 h1.le t
    rwa [one_div, Real.rpow_inv_natCast_pow hc0 (by omega)] at hpow
  obtain ⟨C, hC, hCev⟩ := Puder.exists_eventually_cogrowth_pow_le_sum k hk (ind m)
    (fun g => by unfold ind; split_ifs <;> norm_num) α 1 hα1 one_pos hν
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCev] with t ht
  refine le_trans ht (le_of_eq ?_)
  unfold ind b word
  rw [Finset.sum_boole]

/-! ## Target -/

theorem _root_.Puder.tendsto_card_primitivityRank_eq_rpow_of_sqrt_lt_dev (k m : ℕ) (hk : 2 ≤ k)
    (hm : m ≤ k) (hlt : Real.sqrt (2 * k - 1) < 2 * m - 1) :
    Tendsto (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m).card : ℝ) ^
          (1 / (t : ℝ))) atTop (𝓝 (2 * m - 1 + (2 * k - 1) / (2 * m - 1))) := by
  show Tendsto (fun t : ℕ => b k m t ^ (1 / (t : ℝ))) atTop _
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    subst this
    have := Real.sqrt_nonneg (2 * (k : ℝ) - 1)
    push_cast at hlt
    linarith
  have hr : StrongConv.rhoStair k m = 2 * m - 1 + (2 * k - 1) / (2 * m - 1) := by
    rw [StrongConv.rhoStair, if_neg (not_le.2 hlt)]
  obtain ⟨hB, hL⟩ := upper k m hk hm1 hm
  rw [hr] at hL
  set q : ℝ := 2 * k - 1 with hq
  set L : ℝ := 2 * m - 1 + q / (2 * m - 1) with hLdef
  have hpos : (0 : ℝ) < 2 * m - 1 := lt_of_le_of_lt (Real.sqrt_nonneg _) hlt
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => eventually_lt_of_limsup_lt (lt_of_le_of_lt hL ha) hB⟩
  -- choose `α` just below `2m - 1`
  have hcont : ContinuousAt (fun α : ℝ => q / α + α) (2 * m - 1) :=
    ((continuousAt_const.div continuousAt_id hpos.ne').add continuousAt_id)
  have h1 : ∀ᶠ α in 𝓝[<] ((2 : ℝ) * m - 1), a < q / α + α ∧ Real.sqrt q < α ∧ α < 2 * m - 1 := by
    have ha' : a < (fun α : ℝ => q / α + α) (2 * m - 1) := by
      simp only; rw [hLdef] at ha; linarith
    exact ((hcont.eventually (lt_mem_nhds ha')).filter_mono nhdsWithin_le_nhds).and
      (((lt_mem_nhds hlt).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)
  obtain ⟨α, hαa, hα1, hα2⟩ := h1.exists
  obtain ⟨C, hC, hCev⟩ := lower k m hk hm hlt α hα1 hα2
  have hα0 : 0 < α := lt_of_le_of_lt (Real.sqrt_nonneg _) hα1
  set β : ℝ := q / α + α with hβ
  have hβ0 : 0 < β := by
    have : 0 < q := by rw [hq]; have : (2 : ℝ) ≤ k := by exact_mod_cast hk
                       linarith
    positivity
  have hlimC : Tendsto (fun t : ℕ => C ^ (1 / (t : ℝ)) * β) atTop (𝓝 β) := by
    have h0 : Tendsto (fun t : ℕ => 1 / (t : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x := C)).rpow h0 (Or.inl hC.ne')
    rw [Real.rpow_zero] at this
    simpa using this.mul_const β
  filter_upwards [hlimC.eventually (lt_mem_nhds hαa), hCev, eventually_ge_atTop 1] with t h2 h3 ht
  refine lt_of_lt_of_le h2 ?_
  calc C ^ (1 / (t : ℝ)) * β = (C * β ^ t) ^ (1 / (t : ℝ)) := by
        rw [Real.mul_rpow hC.le (by positivity), one_div,
          Real.pow_rpow_inv_natCast hβ0.le (by omega)]
    _ ≤ b k m t ^ (1 / (t : ℝ)) := Real.rpow_le_rpow (by positivity) h3 (by positivity)

end Puder.Q263T85L

theorem solution : type_of% @Puder.tendsto_card_primitivityRank_eq_rpow_of_sqrt_lt_dev := @Puder.tendsto_card_primitivityRank_eq_rpow_of_sqrt_lt_dev
