-- Prove2me | solution 1 for SubspaceEvasion312.Explicit.design_list_recovery
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T17:13:22.352594+00:00
-- url     : https://prove2.me/submissions/9b14b46e-da54-48ba-976a-b5f422d502cf

import Mathlib
import Definitions.Def_SubspaceEvasion312_Explicit_algebra

section
set_option autoImplicit false
noncomputable section
open Real Finset

namespace SubspaceEvasion312.Explicit.Dev.DLR

variable {V : Type} [Fintype V] {Z : Type}

/-- The mass of the weights `p` on the fibre `g = z`. -/
def fib (p : V → ℝ) (g : V → Z) (z : Z) : ℝ := by
  classical exact ∑ v ∈ univ.filter (fun v => g v = z), p v

/-- Homogeneous (unnormalised) Shannon entropy of `g` under weights `p`:
`∑_z P_z log (P / P_z)` written with `negMulLog`. -/
def ent (p : V → ℝ) (g : V → Z) : ℝ := by
  classical exact (∑ z ∈ univ.image g, negMulLog (fib p g z)) - negMulLog (∑ v, p v)

/-- `p` restricted to the fibre `h = z`. -/
def restr (p : V → ℝ) (h : V → Z) (z : Z) : V → ℝ := by
  classical exact fun v => if h v = z then p v else 0

end SubspaceEvasion312.Explicit.Dev.DLR
end
end

section
set_option autoImplicit false
noncomputable section
open Real Finset

namespace SubspaceEvasion312.Explicit.Dev.DLR

/-- Log-sum inequality. -/
theorem logsum {κ : Type} (s : Finset κ) (a b : κ → ℝ) (ha : ∀ k ∈ s, 0 ≤ a k)
    (hb : ∀ k ∈ s, 0 ≤ b k) (hab : ∀ k ∈ s, 0 < a k → 0 < b k) :
    ∑ k ∈ s, a k * log (b k / a k) ≤ (∑ k ∈ s, a k) * log ((∑ k ∈ s, b k) / ∑ k ∈ s, a k) := by
  set A := ∑ k ∈ s, a k with hA
  set B := ∑ k ∈ s, b k with hB
  have hA0 : 0 ≤ A := sum_nonneg ha
  rcases hA0.eq_or_lt with h0 | hApos
  · have hz : ∀ k ∈ s, a k = 0 := (sum_eq_zero_iff_of_nonneg ha).1 h0.symm
    rw [← h0, zero_mul]
    exact le_of_eq (sum_eq_zero fun k hk => by rw [hz k hk, zero_mul])
  · obtain ⟨k0, hk0, hak0⟩ : ∃ k ∈ s, 0 < a k := by
      by_contra hcon
      push Not at hcon
      have : A ≤ 0 := sum_nonpos fun k hk => hcon k hk
      linarith
    have hBpos : 0 < B := lt_of_lt_of_le (hab k0 hk0 hak0) (single_le_sum hb hk0)
    have key : ∀ k ∈ s, a k * log (b k / a k) ≤ a k * log (B / A) + (b k * A / B - a k) := by
      intro k hk
      rcases (ha k hk).eq_or_lt with h | h
      · rw [← h]
        have : 0 ≤ b k * A / B := div_nonneg (mul_nonneg (hb k hk) hA0) hBpos.le
        simp only [zero_mul, zero_add, sub_zero]
        exact this
      · have hbk := hab k hk h
        have hy : 0 < (b k / a k) / (B / A) := by positivity
        have e : log (b k / a k) = log ((b k / a k) / (B / A)) + log (B / A) := by
          rw [← log_mul hy.ne' (by positivity)]
          congr 1
          field_simp
        have hl := log_le_sub_one_of_pos hy
        have e2 : a k * ((b k / a k) / (B / A) - 1) = b k * A / B - a k := by
          field_simp
        have := mul_le_mul_of_nonneg_left hl h.le
        rw [e, mul_add]
        linarith
    calc ∑ k ∈ s, a k * log (b k / a k)
        ≤ ∑ k ∈ s, (a k * log (B / A) + (b k * A / B - a k)) := sum_le_sum key
      _ = A * log (B / A) := by
        rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← sum_div, ← sum_mul]
        rw [← hA, ← hB]
        field_simp
        ring

variable {V : Type} [Fintype V]

theorem fib_eq {Z : Type} [DecidableEq Z] (p : V → ℝ) (g : V → Z) (z : Z) :
    fib p g z = ∑ v, if g v = z then p v else 0 := by
  unfold fib
  rw [sum_filter]
  congr!

theorem ent_eq {Z : Type} [DecidableEq Z] (p : V → ℝ) (g : V → Z) :
    ent p g = ∑ z ∈ univ.image g, negMulLog (fib p g z) - negMulLog (∑ v, p v) := by
  unfold ent
  congr!

omit [Fintype V] in
theorem restr_apply {Z : Type} [DecidableEq Z] (p : V → ℝ) (h : V → Z) (z : Z) (v : V) :
    restr p h z v = if h v = z then p v else 0 := by
  unfold restr
  congr!

theorem sum_fib {Z : Type} [DecidableEq Z] (p : V → ℝ) (g : V → Z) (t : Finset Z) :
    ∑ z ∈ t, fib p g z = ∑ v, if g v ∈ t then p v else 0 := by
  simp_rw [fib_eq]
  rw [sum_comm]
  exact sum_congr rfl fun v _ => sum_ite_eq t (g v) _

theorem fib_nonneg {Z : Type} (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (g : V → Z) (z : Z) :
    0 ≤ fib p g z := by
  classical
  rw [fib_eq]
  exact sum_nonneg fun v _ => by split_ifs <;> simp [hp v]

theorem sum_eq_sum_fib {Z : Type} [DecidableEq Z] (p : V → ℝ) (g : V → Z) :
    ∑ v, p v = ∑ z ∈ univ.image g, fib p g z := by
  rw [sum_fib]
  simp

theorem ent_zero {Z : Type} (g : V → Z) : ent (fun _ => (0 : ℝ)) g = 0 := by
  classical
  rw [ent_eq]
  simp [fib_eq]

theorem nml_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog (x + y) ≤ negMulLog x + negMulLog y := by
  simp only [negMulLog]
  have h1 : x * log x ≤ x * log (x + y) := by
    rcases hx.eq_or_lt with h | h
    · simp [← h]
    · exact mul_le_mul_of_nonneg_left (log_le_log h (by linarith)) h.le
  have h2 : y * log y ≤ y * log (x + y) := by
    rcases hy.eq_or_lt with h | h
    · simp [← h]
    · exact mul_le_mul_of_nonneg_left (log_le_log h (by linarith)) h.le
  have : -(x + y) * log (x + y) = -(x * log (x + y)) - y * log (x + y) := by ring
  rw [this]
  linarith

theorem nml_sum_le {ι : Type} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    negMulLog (∑ i ∈ s, f i) ≤ ∑ i ∈ s, negMulLog (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, sum_insert hj]
    have h1 : 0 ≤ f j := hf j (mem_insert_self _ _)
    have h2 : 0 ≤ ∑ i ∈ s, f i := sum_nonneg fun i hi => hf i (mem_insert_of_mem hi)
    have := ih fun i hi => hf i (mem_insert_of_mem hi)
    linarith [nml_add_le h1 h2]

theorem ent_nonneg {Z : Type} (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (g : V → Z) : 0 ≤ ent p g := by
  classical
  rw [ent_eq, sum_eq_sum_fib p g]
  have := nml_sum_le (univ.image g) (fib p g) fun z _ => fib_nonneg p hp g z
  linarith

theorem ent_chain {Z Z' : Type} (p : V → ℝ) (g : V → Z) (h : V → Z')
    (hgh : ∀ v w, g v = g w → h v = h w) :
    ent p g = ent p h + ∑ z ∈ (by classical exact univ.image h), ent (restr p h z) g := by
  classical
  rw [ent_eq p g, ent_eq p h]
  have hr : ∀ z, ent (restr p h z) g =
      ∑ w ∈ univ.image g, negMulLog (fib (restr p h z) g w) - negMulLog (fib p h z) := by
    intro z
    rw [ent_eq]
    congr 2
    rw [fib_eq]
    exact sum_congr rfl fun v _ => restr_apply p h z v
  rw [sum_congr rfl (fun z _ => hr z), sum_sub_distrib, sum_comm]
  have key : ∀ w ∈ univ.image g,
      ∑ z ∈ univ.image h, negMulLog (fib (restr p h z) g w) = negMulLog (fib p g w) := by
    intro w hw
    obtain ⟨v0, -, rfl⟩ := mem_image.1 hw
    have hf : ∀ z, fib (restr p h z) g (g v0) = if h v0 = z then fib p g (g v0) else 0 := by
      intro z
      rw [fib_eq, fib_eq]
      split_ifs with hz
      · refine sum_congr rfl fun v _ => ?_
        rw [restr_apply]
        by_cases hv : g v = g v0
        · simp [hv, hgh v v0 hv, hz]
        · simp [hv]
      · refine sum_eq_zero fun v _ => ?_
        rw [restr_apply]
        by_cases hv : g v = g v0
        · simp [hv, hgh v v0 hv, hz]
        · simp [hv]
    simp_rw [hf]
    rw [sum_eq_single (h v0)]
    · simp
    · intro z _ hz
      rw [if_neg (Ne.symm hz), negMulLog_zero]
    · intro hn
      exact absurd (mem_image_of_mem h (mem_univ v0)) hn
  rw [sum_congr rfl key]
  ring

theorem mlog_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * log ((x + y) / x) = x * log (x + y) - x * log x := by
  rcases hx.eq_or_lt with h | h
  · simp [← h]
  · rw [log_div (by linarith) h.ne']
    ring

theorem fxy {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog (x + y) =
      negMulLog x + negMulLog y - (x * log ((x + y) / x) + y * log ((x + y) / y)) := by
  rw [mlog_eq hx hy, add_comm x y, mlog_eq hy hx]
  simp only [negMulLog]
  ring

theorem ent_add_le {Z : Type} (p q : V → ℝ) (hp : ∀ v, 0 ≤ p v) (hq : ∀ v, 0 ≤ q v)
    (g : V → Z) : ent p g + ent q g ≤ ent (fun v => p v + q v) g := by
  classical
  rw [ent_eq, ent_eq, ent_eq]
  have hf : ∀ z, fib (fun v => p v + q v) g z = fib p g z + fib q g z := by
    intro z
    rw [fib_eq, fib_eq, fib_eq, ← sum_add_distrib]
    refine sum_congr rfl fun v _ => ?_
    split_ifs <;> simp
  simp_rw [hf]
  rw [sum_add_distrib, sum_eq_sum_fib p g, sum_eq_sum_fib q g]
  set I := univ.image g
  have hP := fun z => fib_nonneg p hp g z
  have hQ := fun z => fib_nonneg q hq g z
  have h1 := logsum I (fun z => fib p g z) (fun z => fib p g z + fib q g z)
    (fun z _ => hP z) (fun z _ => add_nonneg (hP z) (hQ z)) (fun z _ h => by linarith [hQ z])
  have h2 := logsum I (fun z => fib q g z) (fun z => fib p g z + fib q g z)
    (fun z _ => hQ z) (fun z _ => add_nonneg (hP z) (hQ z)) (fun z _ h => by linarith [hP z])
  simp only [sum_add_distrib] at h1 h2
  rw [sum_congr rfl (fun z _ => fxy (hP z) (hQ z)),
    fxy (sum_nonneg fun z _ => hP z) (sum_nonneg fun z _ => hQ z)]
  rw [sum_sub_distrib, sum_add_distrib, sum_add_distrib]
  linarith

theorem ent_sum_le {Z ι : Type} (J : Finset ι) (P : ι → V → ℝ) (hP : ∀ j ∈ J, ∀ v, 0 ≤ P j v)
    (g : V → Z) : ∑ j ∈ J, ent (P j) g ≤ ent (fun v => ∑ j ∈ J, P j v) g := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact ent_nonneg _ (fun _ => le_rfl) g
  | insert j J hj ih =>
    rw [sum_insert hj]
    simp_rw [sum_insert hj]
    have ih' := ih fun i hi => hP i (mem_insert_of_mem hi)
    have := ent_add_le (P j) (fun v => ∑ i ∈ J, P i v) (hP j (mem_insert_self _ _))
      (fun v => sum_nonneg fun i hi => hP i (mem_insert_of_mem hi) v) g
    linarith

/-- Conditioning on a finer variable `k` lowers the conditional entropy. -/
theorem ent_cond_mono {Z Z' Z'' : Type} (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (g : V → Z)
    (h : V → Z') (k : V → Z'') (hkh : ∀ v w, k v = k w → h v = h w) :
    ∑ z ∈ (by classical exact univ.image k), ent (restr p k z) g ≤
      ∑ z ∈ (by classical exact univ.image h), ent (restr p h z) g := by
  classical
  have hdec : ∀ z, restr p h z = fun v => ∑ z'' ∈ univ.image k, restr (restr p k z'') h z v := by
    intro z
    funext v
    simp only [restr_apply]
    by_cases hz : h v = z <;> simp [hz]
  have hnn : ∀ z'' z, ∀ v, 0 ≤ restr (restr p k z'') h z v := by
    intro z'' z v
    simp only [restr_apply]
    split_ifs <;> simp [hp v]
  have step : ∀ z ∈ univ.image h,
      ∑ z'' ∈ univ.image k, ent (restr (restr p k z'') h z) g ≤ ent (restr p h z) g := by
    intro z _
    rw [hdec z]
    exact ent_sum_le _ _ (fun z'' _ v => hnn z'' z v) g
  refine le_trans ?_ (sum_le_sum step)
  rw [sum_comm]
  refine le_of_eq (sum_congr rfl fun w hw => ?_)
  obtain ⟨v0, -, rfl⟩ := mem_image.1 hw
  have he : ∀ z, ent (restr (restr p k (k v0)) h z) g =
      if h v0 = z then ent (restr p k (k v0)) g else 0 := by
    intro z
    split_ifs with hz
    · congr 1
      funext v
      simp only [restr_apply]
      by_cases hv : k v = k v0
      · simp [hv, hkh v v0 hv, hz]
      · simp [hv]
    · rw [show restr (restr p k (k v0)) h z = fun _ => 0 from ?_]
      · exact ent_zero g
      funext v
      simp only [restr_apply]
      by_cases hv : k v = k v0
      · simp [hv, hkh v v0 hv, hz]
      · simp [hv]
  simp_rw [he]
  rw [sum_ite_eq]
  simp

theorem ent_const {Z : Type} (p : V → ℝ) (g : V → Z)
    (H : ∀ v w, p v ≠ 0 → p w ≠ 0 → g v = g w) : ent p g = 0 := by
  classical
  by_cases hex : ∃ v0, p v0 ≠ 0
  · obtain ⟨v0, hv0⟩ := hex
    have hf : ∀ z, fib p g z = if g v0 = z then ∑ v, p v else 0 := by
      intro z
      rw [fib_eq]
      split_ifs with hz
      · refine sum_congr rfl fun v _ => ?_
        rcases eq_or_ne (p v) 0 with h0 | h0
        · simp [h0]
        · simp [H v v0 h0 hv0, hz]
      · refine sum_eq_zero fun v _ => ?_
        rcases eq_or_ne (p v) 0 with h0 | h0
        · simp [h0]
        · simp [H v v0 h0 hv0, hz]
    rw [ent_eq]
    simp_rw [hf]
    rw [sum_eq_single (g v0)]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), negMulLog_zero]
    · intro hn
      exact absurd (mem_image_of_mem g (mem_univ v0)) hn
  · push Not at hex
    rw [show p = fun _ => 0 from funext hex]
    exact ent_zero g

theorem ent_congr {Z Z' : Type} (p : V → ℝ) (g : V → Z) (g' : V → Z')
    (H : ∀ v w, p v ≠ 0 → p w ≠ 0 → (g v = g w ↔ g' v = g' w)) : ent p g = ent p g' := by
  classical
  have supp : ∀ {Y : Type} (f : V → Y) (z : Y) (v : V), restr p f z v ≠ 0 → f v = z ∧ p v ≠ 0 := by
    intro Y f z v hv
    rw [restr_apply] at hv
    by_cases h1 : f v = z
    · rw [if_pos h1] at hv
      exact ⟨h1, hv⟩
    · rw [if_neg h1] at hv
      exact absurd rfl hv
  have c1 := ent_chain p (fun v => (g v, g' v)) g (fun v w hvw => (Prod.ext_iff.1 hvw).1)
  have c2 := ent_chain p (fun v => (g v, g' v)) g' (fun v w hvw => (Prod.ext_iff.1 hvw).2)
  rw [sum_eq_zero, add_zero] at c1 c2
  · exact c1.symm.trans c2
  · intro z _
    refine ent_const _ _ fun v w hv hw => ?_
    obtain ⟨h1, hv'⟩ := supp g' z v hv
    obtain ⟨h2, hw'⟩ := supp g' z w hw
    exact Prod.ext ((H v w hv' hw').2 (h1.trans h2.symm)) (h1.trans h2.symm)
  · intro z _
    refine ent_const _ _ fun v w hv hw => ?_
    obtain ⟨h1, hv'⟩ := supp g z v hv
    obtain ⟨h2, hw'⟩ := supp g z w hw
    exact Prod.ext (h1.trans h2.symm) ((H v w hv' hw').1 (h1.trans h2.symm))

theorem ent_indicator [DecidableEq V] (T : Finset V) :
    ent (fun v => if v ∈ T then (1 : ℝ) else 0) id = T.card * log T.card := by
  rw [ent_eq]
  have hf : ∀ z, fib (fun v => if v ∈ T then (1 : ℝ) else 0) id z = if z ∈ T then 1 else 0 := by
    intro z
    rw [fib_eq]
    simp
  simp_rw [hf]
  rw [sum_eq_zero]
  · simp [negMulLog]
  · intro z _
    split_ifs <;> simp

/-- The bound on the entropy of one coordinate used in the list-recovery theorem:
at most `ℓ` fibres carry the `n` points landing in `S`, the others have mass at least one. -/
theorem ent_split_bound [DecidableEq V] {Z : Type} [DecidableEq Z] (T : Finset V) (g : V → Z) (S : Finset Z) (ℓ : ℕ)
    (hS : S.card ≤ ℓ) :
    ent (fun v => if v ∈ T then (1 : ℝ) else 0) g ≤
      ((T.card : ℝ) - (T.filter (fun v => g v ∈ S)).card) * log T.card +
      ((T.filter (fun v => g v ∈ S)).card : ℝ) *
        log ((ℓ : ℝ) * T.card / (T.filter (fun v => g v ∈ S)).card) := by
  set p : V → ℝ := fun v => if v ∈ T then (1 : ℝ) else 0 with hp
  set n := (T.filter (fun v => g v ∈ S)).card with hn
  set N := T.card with hN
  have hfibnat : ∀ z, fib p g z = ((T.filter (fun v => g v = z)).card : ℝ) := by
    intro z
    rw [fib_eq]
    simp only [hp, ← ite_and]
    rw [sum_boole]
    congr 2
    ext v
    simp [and_comm]
  have htot : ∑ v, p v = N := by simp [hp, hN]
  rw [ent_eq, htot]
  set I := univ.image g
  rw [← sum_filter_add_sum_filter_not I (· ∈ S)]
  set S' := I.filter (· ∈ S) with hS'
  have hA : ∑ z ∈ I.filter (fun z => z ∉ S), negMulLog (fib p g z) ≤ 0 := by
    refine sum_nonpos fun z _ => ?_
    rw [hfibnat, negMulLog]
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) (T.filter (fun v => g v = z)).card)
      (log_natCast_nonneg (T.filter (fun v => g v = z)).card)
    linarith
  have hsum : ∑ z ∈ S', fib p g z = n := by
    rw [sum_fib]
    have : ∀ v, (g v ∈ S') ↔ g v ∈ S := fun v => by simp [hS', I]
    simp only [this, hp, ← ite_and]
    rw [sum_boole]
    congr 2
    ext v
    simp [and_comm]
  have hB : ∑ z ∈ S', negMulLog (fib p g z) = ∑ z ∈ S', fib p g z * log (1 / fib p g z) := by
    refine sum_congr rfl fun z _ => ?_
    simp [negMulLog, log_inv]
  have hlog := logsum S' (fun z => fib p g z) (fun _ => 1)
    (fun z _ => fib_nonneg p (fun v => by simp only [hp]; split_ifs <;> norm_num) g z)
    (fun _ _ => zero_le_one) (fun _ _ _ => one_pos)
  simp only [sum_const, nsmul_eq_mul, mul_one] at hlog
  rw [hsum, ← hB] at hlog
  have hnml : negMulLog (N : ℝ) = -(N * log N) := by simp [negMulLog]
  rw [hnml]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at hlog ⊢
    simp only [Nat.cast_zero, zero_mul, sub_zero] at hlog ⊢
    linarith
  · have hS'card : 0 < S'.card := by
      rcases S'.eq_empty_or_nonempty with he | hne
      · rw [he, sum_empty] at hsum
        have : (0 : ℝ) < n := by exact_mod_cast hpos
        linarith
      · exact hne.card_pos
    have hS'le : S'.card ≤ ℓ := le_trans (card_le_card fun z hz => (mem_filter.1 hz).2) hS
    have hnN : n ≤ N := card_filter_le _ _
    have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
    have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hpos hnN)
    have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast (lt_of_lt_of_le hS'card hS'le)
    have hmono : log ((S'.card : ℝ) / n) ≤ log ((ℓ : ℝ) / n) := by
      apply log_le_log (by positivity)
      exact div_le_div_of_nonneg_right (by exact_mod_cast hS'le) hnR.le
    have hsplit : log ((ℓ : ℝ) * N / n) = log ((ℓ : ℝ) / n) + log N := by
      rw [show (ℓ : ℝ) * N / n = ((ℓ : ℝ) / n) * N by ring, log_mul (by positivity) hNR.ne']
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left hmono hnR.le
    nlinarith

end SubspaceEvasion312.Explicit.Dev.DLR
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Real Finset Module

namespace SubspaceEvasion312.Explicit.Dev.DLR

/-- The generic "largest λ" lemma for finitely many affine constraints `a c + λ b c ≥ 0`. -/
theorem bl_lambda {κ : Type} [Finite κ] (a b : κ → ℝ) (ha : ∀ c, 0 ≤ a c)
    (hab : ∀ c, b c < 0 → 0 < a c) (hneg : ∃ c, b c < 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ c, 0 ≤ a c + t * b c) ∧ ∃ c, b c < 0 ∧ a c + t * b c = 0 := by
  obtain ⟨c0, hc0, hmin⟩ := Set.exists_min_image {c | b c < 0} (fun c => a c / (-b c))
    (Set.toFinite _) hneg
  have hc0' : b c0 < 0 := hc0
  have hb0 : 0 < -b c0 := neg_pos.2 hc0'
  have ht : 0 < a c0 / -b c0 := div_pos (hab c0 hc0') hb0
  refine ⟨a c0 / (-b c0), ht, ?_, c0, hc0', ?_⟩
  · intro c
    by_cases hc : b c < 0
    · have h1 : a c0 / -b c0 ≤ a c / -b c := hmin c hc
      have hb : 0 < -b c := neg_pos.2 hc
      rw [le_div_iff₀ hb] at h1
      nlinarith
    · push Not at hc
      nlinarith [ha c, mul_nonneg ht.le hc]
  · rw [div_neg, neg_mul, div_mul_cancel₀ _ hc0'.ne]
    ring

theorem bl_sum_lin {ι : Type} [Fintype ι] (s δ x : ι → ℝ) (t : ℝ) :
    ∑ i, (s i + t * δ i) * x i = ∑ i, s i * x i + t * ∑ i, δ i * x i := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem bl_sum_alg {κ Zt : Type} [Fintype κ] (Z : Finset Zt) (s : κ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (E EW : ℝ) (Ez : Zt → ℝ) (HW : κ → ℝ) (Hz : Zt → κ → ℝ) (H : κ → ℝ)
    (hch : E = EW + ∑ z ∈ Z, Ez z) (hup : EW ≤ ∑ i, s i * HW i)
    (hlow : ∀ z ∈ Z, Ez z ≤ ∑ i, s i * Hz z i) (hrhs : ∀ i, HW i + ∑ z ∈ Z, Hz z i ≤ H i) :
    E ≤ ∑ i, s i * H i := by
  calc E = EW + ∑ z ∈ Z, Ez z := hch
    _ ≤ ∑ i, s i * HW i + ∑ z ∈ Z, ∑ i, s i * Hz z i := add_le_add hup (Finset.sum_le_sum hlow)
    _ = ∑ i, s i * (HW i + ∑ z ∈ Z, Hz z i) := by
        rw [Finset.sum_comm, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_add, Finset.mul_sum]
    _ ≤ ∑ i, s i * H i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrhs i) (hs i)

section BL

variable {F : Type} [Field F] [Fintype F] {V Y ι : Type} [AddCommGroup V] [Module F V]
    [Fintype V] [AddCommGroup Y] [Module F Y] [Fintype ι]

/-- `e_i(W) = dim pr_i W - dim pr_i B`. -/
def bl_e (pr : ι → V →ₗ[F] Y) (B W : Submodule F V) (i : ι) : ℝ :=
  (finrank F (W.map (pr i)) : ℝ) - finrank F (B.map (pr i))

/-- `d(W) = dim W - dim B`. -/
def bl_d (B W : Submodule F V) : ℝ := (finrank F W : ℝ) - finrank F B

def bl_C (pr : ι → V →ₗ[F] Y) (s : ι → ℝ) (B A : Submodule F V) : Prop :=
  ∀ W : Submodule F V, B ≤ W → W ≤ A → bl_d B W ≤ ∑ i, s i * bl_e pr B W i

def bl_h (pr : ι → V →ₗ[F] Y) (B : Submodule F V) (p : V → ℝ) (i : ι) : ℝ :=
  ent p (fun v => (B.map (pr i)).mkQ (pr i v))

def bl_G (pr : ι → V →ₗ[F] Y) (s : ι → ℝ) (B : Submodule F V) (p : V → ℝ) : Prop :=
  ent p B.mkQ ≤ ∑ i, s i * bl_h pr B p i

def bl_P (pr : ι → V →ₗ[F] Y) (B A : Submodule F V) : Prop :=
  ∀ s : ι → ℝ, (∀ i, 0 ≤ s i) → bl_C pr s B A → ∀ p : V → ℝ, (∀ v, 0 ≤ p v) → ∀ a : V,
    (∀ v, p v ≠ 0 → v - a ∈ A) → bl_G pr s B p

theorem bl_e_self (pr : ι → V →ₗ[F] Y) (B : Submodule F V) (i : ι) : bl_e pr B B i = 0 :=
  sub_self _

theorem bl_e_mono (pr : ι → V →ₗ[F] Y) (B W W' : Submodule F V) (h : W ≤ W') (i : ι) :
    bl_e pr B W i ≤ bl_e pr B W' i := by
  unfold bl_e
  have := Submodule.finrank_mono (Submodule.map_mono (f := pr i) h)
  have : (finrank F (W.map (pr i)) : ℝ) ≤ finrank F (W'.map (pr i)) := by exact_mod_cast this
  linarith

theorem bl_e_nonneg (pr : ι → V →ₗ[F] Y) (B W : Submodule F V) (h : B ≤ W) (i : ι) :
    0 ≤ bl_e pr B W i := by
  have := bl_e_mono pr B B W h i
  rwa [bl_e_self] at this

theorem bl_rn (f : V →ₗ[F] Y) (W : Submodule F V) :
    finrank F (W.map f) + finrank F (W ⊓ LinearMap.ker f : Submodule F V) = finrank F W := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict W)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq W, Submodule.map_comap_subtype] at h
  exact h

theorem bl_e_le_d (pr : ι → V →ₗ[F] Y) (B A : Submodule F V) (h : B ≤ A) (i : ι) :
    bl_e pr B A i ≤ bl_d B A := by
  unfold bl_e bl_d
  have h1 := bl_rn (pr i) A
  have h2 := bl_rn (pr i) B
  have h3 := Submodule.finrank_mono (inf_le_inf_right (LinearMap.ker (pr i)) h)
  have h1' : ((finrank F (A.map (pr i)) : ℕ) : ℝ) + finrank F (A ⊓ LinearMap.ker (pr i) :
    Submodule F V) = finrank F A := by exact_mod_cast h1
  have h2' : ((finrank F (B.map (pr i)) : ℕ) : ℝ) + finrank F (B ⊓ LinearMap.ker (pr i) :
    Submodule F V) = finrank F B := by exact_mod_cast h2
  have h3' : (finrank F (B ⊓ LinearMap.ker (pr i) : Submodule F V) : ℝ) ≤
    finrank F (A ⊓ LinearMap.ker (pr i) : Submodule F V) := by exact_mod_cast h3
  linarith

theorem bl_d_pos (B A : Submodule F V) (h : B ≤ A) (hne : B ≠ A) : 0 < bl_d B A := by
  unfold bl_d
  have := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne h hne)
  have : (finrank F B : ℝ) < finrank F A := by exact_mod_cast this
  linarith

theorem bl_h_nonneg (pr : ι → V →ₗ[F] Y) (B : Submodule F V) (p : V → ℝ) (hp : ∀ v, 0 ≤ p v)
    (i : ι) : 0 ≤ bl_h pr B p i :=
  ent_nonneg p hp _

theorem bl_rhs_nonneg (pr : ι → V →ₗ[F] Y) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (B : Submodule F V)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) : 0 ≤ ∑ i, s i * bl_h pr B p i :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hs i) (bl_h_nonneg pr B p hp i)

theorem bl_mkQ_eq (B : Submodule F V) (v w : V) : B.mkQ v = B.mkQ w ↔ v - w ∈ B := by
  simp only [Submodule.mkQ_apply]
  exact Submodule.Quotient.eq B

theorem bl_mkQ_eq' (C : Submodule F Y) (v w : Y) : C.mkQ v = C.mkQ w ↔ v - w ∈ C := by
  simp only [Submodule.mkQ_apply]
  exact Submodule.Quotient.eq C

/-- The section `A = B`: everything lies in one coset of `B`. -/
theorem bl_same (pr : ι → V →ₗ[F] Y) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (B : Submodule F V)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (a : V) (hsupp : ∀ v, p v ≠ 0 → v - a ∈ B) :
    bl_G pr s B p := by
  unfold bl_G
  rw [ent_const p B.mkQ]
  · exact bl_rhs_nonneg pr s hs B p hp
  · intro v w hv hw
    rw [bl_mkQ_eq]
    have := B.sub_mem (hsupp v hv) (hsupp w hw)
    rwa [sub_sub_sub_cancel_right] at this

/-- A single support element. -/
theorem bl_single (pr : ι → V →ₗ[F] Y) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (B A : Submodule F V)
    (hBA : B ≤ A) (hne : B ≠ A) (hC : bl_C pr s B A)
    (hk : (univ.filter fun i => s i ≠ 0).card ≤ 1)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (a : V) (hsupp : ∀ v, p v ≠ 0 → v - a ∈ A) :
    bl_G pr s B p := by
  have hd := bl_d_pos B A hBA hne
  have hCA := hC A hBA le_rfl
  -- the support is a singleton
  obtain ⟨i, hi⟩ : ∃ i, ∀ j, j ≠ i → s j = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with h0 | h1
    · exfalso
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      have : ∑ i, s i * bl_e pr B A i = 0 :=
        Finset.sum_eq_zero fun i _ => by
          have := h0 (Finset.mem_univ i); push Not at this; simp [this]
      linarith
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h1
      refine ⟨i, fun j hj => ?_⟩
      by_contra hsj
      have : j ∈ univ.filter (fun i => s i ≠ 0) := by simp [hsj]
      rw [hi, Finset.mem_singleton] at this
      exact hj this
  have hsum : ∀ x : ι → ℝ, ∑ j, s j * x j = s i * x i := fun x =>
    Finset.sum_eq_single i (fun j _ hj => by simp [hi j hj]) (by simp)
  rw [hsum] at hCA
  have he := bl_e_le_d pr B A hBA i
  have he0 := bl_e_nonneg pr B A hBA i
  have hs1 : 1 ≤ s i := by
    by_contra h
    push Not at h
    nlinarith [hs i]
  -- the key: on `A`, `pr i x ∈ pr i B` forces `x ∈ B`
  have key : ∀ x ∈ A, pr i x ∈ B.map (pr i) → x ∈ B := by
    set K : Submodule F V := A ⊓ (B ⊔ LinearMap.ker (pr i)) with hK
    have hBK : B ≤ K := le_inf hBA le_sup_left
    have hKmap : K.map (pr i) ≤ B.map (pr i) := by
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨b, hb, k, hk, hbk⟩ := Submodule.mem_sup.1 (Submodule.mem_inf.1 hx).2
      rw [← hbk, map_add, LinearMap.mem_ker.1 hk, add_zero]
      exact Submodule.mem_map_of_mem hb
    have hCK := hC K hBK inf_le_left
    rw [hsum] at hCK
    have heK : bl_e pr B K i ≤ 0 := by
      unfold bl_e
      have := Submodule.finrank_mono hKmap
      have : (finrank F (K.map (pr i)) : ℝ) ≤ finrank F (B.map (pr i)) := by exact_mod_cast this
      linarith
    have : bl_d B K ≤ 0 := by nlinarith [hs i]
    unfold bl_d at this
    have hle : finrank F K ≤ finrank F B := by
      have : (finrank F K : ℝ) ≤ finrank F B := by linarith
      exact_mod_cast this
    have hKB : B = K := Submodule.eq_of_le_of_finrank_le hBK hle
    intro x hxA hxm
    obtain ⟨b, hb, hfb⟩ := Submodule.mem_map.1 hxm
    rw [hKB]
    refine Submodule.mem_inf.2 ⟨hxA, Submodule.mem_sup.2 ⟨b, hb, x - b, ?_, by abel⟩⟩
    rw [LinearMap.mem_ker, map_sub, hfb, sub_self]
  unfold bl_G
  rw [hsum]
  have hEq : ent p B.mkQ = bl_h pr B p i := by
    unfold bl_h
    apply ent_congr
    intro v w hv hw
    rw [bl_mkQ_eq, bl_mkQ_eq', ← map_sub]
    have hvw : v - w ∈ A := by
      have := A.sub_mem (hsupp v hv) (hsupp w hw)
      rwa [sub_sub_sub_cancel_right] at this
    exact ⟨fun h => Submodule.mem_map_of_mem h, fun h => key _ hvw h⟩
  rw [hEq]
  have := bl_h_nonneg pr B p hp i
  nlinarith

/-- Case 1: a proper tight `W`. -/
theorem bl_case1 (pr : ι → V →ₗ[F] Y) (B A : Submodule F V)
    (IHn : ∀ B' A' : Submodule F V, B' ≤ A' →
      finrank F A' - finrank F B' < finrank F A - finrank F B → bl_P pr B' A')
    (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (hC : bl_C pr s B A)
    (W : Submodule F V) (hBW : B ≤ W) (hWA : W ≤ A) (hWB : W ≠ B) (hWA' : W ≠ A)
    (htight : bl_d B W = ∑ i, s i * bl_e pr B W i)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (a : V) (hsupp : ∀ v, p v ≠ 0 → v - a ∈ A) :
    bl_G pr s B p := by
  have hBlt : finrank F B < finrank F W :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hBW (Ne.symm hWB))
  have hWlt : finrank F W < finrank F A :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hWA hWA')
  -- the upper section `(W, A)`
  have hCWA : bl_C pr s W A := by
    intro W' h1 h2
    have h3 := hC W' (hBW.trans h1) h2
    unfold bl_d bl_e at *
    have : ∑ i, s i * ((finrank F (W'.map (pr i)) : ℝ) - finrank F (W.map (pr i))) =
        ∑ i, s i * ((finrank F (W'.map (pr i)) : ℝ) - finrank F (B.map (pr i))) -
        ∑ i, s i * ((finrank F (W.map (pr i)) : ℝ) - finrank F (B.map (pr i))) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    linarith
  have hup : ent p W.mkQ ≤ ∑ i, s i * bl_h pr W p i :=
    IHn W A hWA (by omega) s hs hCWA p hp a hsupp
  have hch := ent_chain p B.mkQ W.mkQ (fun v w h => by
    rw [bl_mkQ_eq] at h ⊢; exact hBW h)
  have hrestr : ∀ z, ∀ v, 0 ≤ restr p W.mkQ z v := fun z v => by
    unfold restr; split_ifs <;> simp [hp v]
  refine bl_sum_alg _ s hs _ _ _ _ (fun z i => bl_h pr B (restr p W.mkQ z) i) _ hch hup ?_ ?_
  · intro z _
    obtain ⟨az, haz⟩ := W.mkQ_surjective z
    refine IHn B W hBW (by omega) s hs (fun W' h1 h2 => hC W' h1 (h2.trans hWA)) _ (hrestr z) az ?_
    intro v hv
    unfold restr at hv
    split_ifs at hv with hvz
    · rw [← bl_mkQ_eq, hvz, haz]
    · exact absurd rfl hv
  · intro i
    have h1 := ent_chain p (fun v => (B.map (pr i)).mkQ (pr i v))
      (fun v => (W.map (pr i)).mkQ (pr i v)) (fun v w h => by
        simp only [bl_mkQ_eq'] at h ⊢
        exact Submodule.map_mono hBW h)
    have h2 := ent_cond_mono p hp (fun v => (B.map (pr i)).mkQ (pr i v))
      (fun v => (W.map (pr i)).mkQ (pr i v)) W.mkQ (fun v w h => by
        simp only [bl_mkQ_eq'] at h ⊢
        rw [← map_sub]
        exact Submodule.mem_map_of_mem h)
    unfold bl_h
    linarith

/-- Moving along a direction `δ` to the largest admissible step. -/
theorem bl_move (pr : ι → V →ₗ[F] Y) (B A : Submodule F V) (s δ : ι → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hC : bl_C pr s B A)
    (hδs : ∀ i, δ i ≠ 0 → s i ≠ 0) (hneg : ∃ i, δ i < 0)
    (hslack : ∀ W : Submodule F V, B ≤ W → W ≤ A → ∑ i, δ i * bl_e pr B W i < 0 →
      bl_d B W < ∑ i, s i * bl_e pr B W i) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ s i + t * δ i) ∧ bl_C pr (fun i => s i + t * δ i) B A ∧
      ((∃ i, s i ≠ 0 ∧ s i + t * δ i = 0) ∨
       (∃ W : Submodule F V, B ≤ W ∧ W ≤ A ∧ ∑ i, δ i * bl_e pr B W i < 0 ∧
          bl_d B W = ∑ i, (s i + t * δ i) * bl_e pr B W i)) := by
  classical
  have : Finite (Submodule F V) :=
    Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective
  let a : Submodule F V ⊕ ι → ℝ := fun c => match c with
    | Sum.inl W => if B ≤ W ∧ W ≤ A then ∑ i, s i * bl_e pr B W i - bl_d B W else 0
    | Sum.inr i => s i
  let b : Submodule F V ⊕ ι → ℝ := fun c => match c with
    | Sum.inl W => if B ≤ W ∧ W ≤ A then ∑ i, δ i * bl_e pr B W i else 0
    | Sum.inr i => δ i
  have ha : ∀ c, 0 ≤ a c := by
    rintro (W | i)
    · simp only [a]
      split_ifs with h
      · linarith [hC W h.1 h.2]
      · exact le_rfl
    · exact hs i
  have hab : ∀ c, b c < 0 → 0 < a c := by
    rintro (W | i) hc
    · simp only [a, b] at hc ⊢
      split_ifs at hc ⊢ with h
      · linarith [hslack W h.1 h.2 hc]
      · exact absurd hc (lt_irrefl 0)
    · exact lt_of_le_of_ne (hs i) (Ne.symm (hδs i hc.ne))
  obtain ⟨i0, hi0⟩ := hneg
  obtain ⟨t, ht, hall, c, hc, hc0⟩ := bl_lambda a b ha hab ⟨Sum.inr i0, hi0⟩
  refine ⟨t, ht, fun i => hall (Sum.inr i), ?_, ?_⟩
  · intro W h1 h2
    have := hall (Sum.inl W)
    simp only [a, b, if_pos (And.intro h1 h2)] at this
    rw [bl_sum_lin]
    linarith
  · rcases c with W | i
    · simp only [a, b] at hc hc0
      split_ifs at hc hc0 with h
      · right
        refine ⟨W, h.1, h.2, hc, ?_⟩
        rw [bl_sum_lin]
        linarith
      · exact absurd hc (lt_irrefl 0)
    · left
      exact ⟨i, fun h => hδs i hc.ne h, hc0⟩

/-- After a move, conclude from the cases at the endpoint. -/
theorem bl_close (pr : ι → V →ₗ[F] Y) (B A : Submodule F V) (p : V → ℝ) (K : ℕ)
    (hIHk : ∀ s' : ι → ℝ, (∀ i, 0 ≤ s' i) → bl_C pr s' B A →
      (univ.filter fun i => s' i ≠ 0).card < K → bl_G pr s' B p)
    (hcase1 : ∀ s' : ι → ℝ, (∀ i, 0 ≤ s' i) → bl_C pr s' B A → ∀ W : Submodule F V,
      B ≤ W → W ≤ A → W ≠ B → W ≠ A → bl_d B W = ∑ i, s' i * bl_e pr B W i → bl_G pr s' B p)
    (s δ : ι → ℝ)
    (hAt : ∑ i, δ i * bl_e pr B A i < 0 → ∀ s' : ι → ℝ, (∀ i, 0 ≤ s' i) → bl_C pr s' B A →
      (univ.filter fun i => s' i ≠ 0).card ≤ K → bl_d B A = ∑ i, s' i * bl_e pr B A i →
      bl_G pr s' B p)
    (hs : ∀ i, 0 ≤ s i) (hC : bl_C pr s B A) (hk : (univ.filter fun i => s i ≠ 0).card ≤ K)
    (hδs : ∀ i, δ i ≠ 0 → s i ≠ 0) (hneg : ∃ i, δ i < 0)
    (hslack : ∀ W : Submodule F V, B ≤ W → W ≤ A → ∑ i, δ i * bl_e pr B W i < 0 →
      bl_d B W < ∑ i, s i * bl_e pr B W i)
    (hδh : ∑ i, δ i * bl_h pr B p i ≤ 0) : bl_G pr s B p := by
  obtain ⟨t, ht, hs', hC', hout⟩ := bl_move pr B A s δ hs hC hδs hneg hslack
  have hsub : (univ.filter fun i => s i + t * δ i ≠ 0) ⊆ univ.filter fun i => s i ≠ 0 := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    intro hsj
    have : δ j = 0 := by
      by_contra h; exact hδs j h hsj
    rw [hsj, this] at hj
    simp at hj
  have hG' : bl_G pr (fun i => s i + t * δ i) B p := by
    rcases hout with ⟨i, hi, hi0⟩ | ⟨W, h1, h2, hsl, htight⟩
    · apply hIHk _ hs' hC'
      refine lt_of_lt_of_le (Finset.card_lt_card ?_) hk
      refine (Finset.ssubset_iff_of_subset hsub).2 ⟨i, ?_, ?_⟩
      · simp [hi]
      · simp [hi0]
    · by_cases hWB : W = B
      · subst hWB
        simp [bl_e_self] at hsl
      by_cases hWA : W = A
      · subst hWA
        exact hAt hsl _ hs' hC' ((Finset.card_le_card hsub).trans hk) htight
      exact hcase1 _ hs' hC' W h1 h2 hWB hWA htight
  unfold bl_G at hG' ⊢
  rw [bl_sum_lin] at hG'
  nlinarith [mul_nonpos_of_nonneg_of_nonpos ht.le hδh]

/-- `A` tight: the single-support case, the zero-out step, or a move along `±δ`. -/
theorem bl_tight (pr : ι → V →ₗ[F] Y) (B A : Submodule F V) (hBA : B ≤ A) (hne : B ≠ A)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (a : V) (hsupp : ∀ v, p v ≠ 0 → v - a ∈ A) (K : ℕ)
    (hIHk : ∀ s' : ι → ℝ, (∀ i, 0 ≤ s' i) → bl_C pr s' B A →
      (univ.filter fun i => s' i ≠ 0).card < K → bl_G pr s' B p)
    (hcase1 : ∀ s' : ι → ℝ, (∀ i, 0 ≤ s' i) → bl_C pr s' B A → ∀ W : Submodule F V,
      B ≤ W → W ≤ A → W ≠ B → W ≠ A → bl_d B W = ∑ i, s' i * bl_e pr B W i → bl_G pr s' B p)
    (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (hC : bl_C pr s B A)
    (hk : (univ.filter fun i => s i ≠ 0).card ≤ K)
    (hA : bl_d B A = ∑ i, s i * bl_e pr B A i) : bl_G pr s B p := by
  by_cases hW : ∃ W : Submodule F V, B ≤ W ∧ W ≤ A ∧ W ≠ B ∧ W ≠ A ∧
      bl_d B W = ∑ i, s i * bl_e pr B W i
  · obtain ⟨W, h1, h2, h3, h4, h5⟩ := hW
    exact hcase1 s hs hC W h1 h2 h3 h4 h5
  push Not at hW
  by_cases hz : ∃ j, s j ≠ 0 ∧ bl_e pr B A j = 0
  · obtain ⟨j, hsj, hej⟩ := hz
    classical
    set s' : ι → ℝ := fun l => if l = j then 0 else s l with hs'def
    have hs' : ∀ i, 0 ≤ s' i := fun i => by
      simp only [hs'def]; split_ifs
      · exact le_rfl
      · exact hs i
    have hejW : ∀ W : Submodule F V, B ≤ W → W ≤ A → bl_e pr B W j = 0 := fun W h1 h2 =>
      le_antisymm (hej ▸ bl_e_mono pr B W A h2 j) (bl_e_nonneg pr B W h1 j)
    have hC' : bl_C pr s' B A := by
      intro W h1 h2
      have := hC W h1 h2
      have heq : ∑ i, s' i * bl_e pr B W i = ∑ i, s i * bl_e pr B W i :=
        Finset.sum_congr rfl fun i _ => by
          simp only [hs'def]
          split_ifs with hij
          · subst hij; rw [hejW W h1 h2]; ring
          · rfl
      rw [heq]; exact this
    have hG' := hIHk s' hs' hC' (by
      refine lt_of_lt_of_le (Finset.card_lt_card ?_) hk
      refine (Finset.ssubset_iff_of_subset ?_).2 ⟨j, ?_, ?_⟩
      · intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs'def] at hl ⊢
        split_ifs at hl
        · exact absurd rfl hl
        · exact hl
      · simp [hsj]
      · simp [hs'def])
    unfold bl_G at hG' ⊢
    refine hG'.trans (Finset.sum_le_sum fun i _ => ?_)
    simp only [hs'def]
    split_ifs
    · rw [zero_mul]; exact mul_nonneg (hs i) (bl_h_nonneg pr B p hp i)
    · exact le_rfl
  push Not at hz
  have hepos : ∀ j, s j ≠ 0 → 0 < bl_e pr B A j := fun j hj =>
    lt_of_le_of_ne (bl_e_nonneg pr B A hBA j) (Ne.symm (hz j hj))
  by_cases h1 : (univ.filter fun i => s i ≠ 0).card ≤ 1
  · exact bl_single pr s hs B A hBA hne hC h1 p hp a hsupp
  push Not at h1
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have hei := hepos i hi
  have hej := hepos j hj
  -- the common closing step for a direction `δ` that keeps `A` tight
  have hgo : ∀ δ : ι → ℝ, (∀ l, δ l ≠ 0 → s l ≠ 0) → (∃ l, δ l < 0) →
      ∑ l, δ l * bl_e pr B A l = 0 → ∑ l, δ l * bl_h pr B p l ≤ 0 → bl_G pr s B p := by
    intro δ hδs hneg hδA hδh
    refine bl_close pr B A p K hIHk hcase1 s δ (fun h => absurd (hδA ▸ h) (lt_irrefl 0))
      hs hC hk hδs hneg ?_ hδh
    intro W h1 h2 hsl
    by_cases hWB : W = B
    · subst hWB; simp [bl_e_self] at hsl
    by_cases hWA : W = A
    · subst hWA; rw [hδA] at hsl; exact absurd hsl (lt_irrefl 0)
    exact lt_of_le_of_ne (hC W h1 h2) (hW W h1 h2 hWB hWA)
  classical
  set δ0 : ι → ℝ := fun l => (if l = i then 1 / bl_e pr B A i else 0) -
    (if l = j then 1 / bl_e pr B A j else 0) with hδ0
  have hsum : ∀ x : ι → ℝ, ∑ l, δ0 l * x l = x i / bl_e pr B A i - x j / bl_e pr B A j := by
    intro x
    simp only [hδ0, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  have hδA : ∑ l, δ0 l * bl_e pr B A l = 0 := by
    rw [hsum, div_self hei.ne', div_self hej.ne', sub_self]
  have hsupp0 : ∀ l, δ0 l ≠ 0 → s l ≠ 0 := by
    intro l hl
    by_cases hli : l = i
    · rw [hli]; exact hi
    by_cases hlj : l = j
    · rw [hlj]; exact hj
    exfalso; apply hl; simp [hδ0, hli, hlj]
  have hδi : δ0 i = 1 / bl_e pr B A i := by simp [hδ0, hij]
  have hδj : δ0 j = -(1 / bl_e pr B A j) := by simp [hδ0, Ne.symm hij]
  by_cases hσ : ∑ l, δ0 l * bl_h pr B p l ≤ 0
  · refine hgo δ0 hsupp0 ⟨j, ?_⟩ hδA hσ
    rw [hδj]; have := one_div_pos.2 hej; linarith
  · push Not at hσ
    refine hgo (fun l => -δ0 l) (fun l hl => hsupp0 l (fun h => hl (by rw [h, neg_zero])))
      ⟨i, ?_⟩ ?_ ?_
    · rw [hδi]; have := one_div_pos.2 hei; linarith
    · simp only [neg_mul, Finset.sum_neg_distrib, hδA, neg_zero]
    · simp only [neg_mul, Finset.sum_neg_distrib]; linarith

/-- `A` not tight: lower one coordinate. -/
theorem bl_nontight (pr : ι → V →ₗ[F] Y) (B A : Submodule F V) (hBA : B ≤ A) (hne : B ≠ A)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (K : ℕ)
    (hIHk : ∀ s' : ι → ℝ, (∀ i, 0 ≤ s' i) → bl_C pr s' B A →
      (univ.filter fun i => s' i ≠ 0).card < K → bl_G pr s' B p)
    (hcase1 : ∀ s' : ι → ℝ, (∀ i, 0 ≤ s' i) → bl_C pr s' B A → ∀ W : Submodule F V,
      B ≤ W → W ≤ A → W ≠ B → W ≠ A → bl_d B W = ∑ i, s' i * bl_e pr B W i → bl_G pr s' B p)
    (hAt : ∀ s' : ι → ℝ, (∀ i, 0 ≤ s' i) → bl_C pr s' B A →
      (univ.filter fun i => s' i ≠ 0).card ≤ K → bl_d B A = ∑ i, s' i * bl_e pr B A i →
      bl_G pr s' B p)
    (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (hC : bl_C pr s B A)
    (hk : (univ.filter fun i => s i ≠ 0).card ≤ K)
    (hA : bl_d B A ≠ ∑ i, s i * bl_e pr B A i) : bl_G pr s B p := by
  by_cases hW : ∃ W : Submodule F V, B ≤ W ∧ W ≤ A ∧ W ≠ B ∧ W ≠ A ∧
      bl_d B W = ∑ i, s i * bl_e pr B W i
  · obtain ⟨W, h1, h2, h3, h4, h5⟩ := hW
    exact hcase1 s hs hC W h1 h2 h3 h4 h5
  push Not at hW
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push Not at h
    have := hC A hBA le_rfl
    simp [h] at this
    linarith [bl_d_pos B A hBA hne]
  classical
  refine bl_close pr B A p K hIHk hcase1 s (fun l => if l = i then -1 else 0) (fun _ => hAt)
    hs hC hk ?_ ⟨i, by simp⟩ ?_ ?_
  · intro l hl
    by_cases hli : l = i
    · rw [hli]; exact hi
    · simp [hli] at hl
  · intro W h1 h2 hsl
    by_cases hWB : W = B
    · subst hWB; simp [bl_e_self] at hsl
    by_cases hWA : W = A
    · subst hWA; exact lt_of_le_of_ne (hC _ h1 h2) hA
    exact lt_of_le_of_ne (hC W h1 h2) (hW W h1 h2 hWB hWA)
  · simp only [ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith [bl_h_nonneg pr B p hp i]

/-- The induction step on `dim A - dim B`. -/
theorem bl_step (pr : ι → V →ₗ[F] Y) (B A : Submodule F V) (hBA : B ≤ A)
    (IHn : ∀ B' A' : Submodule F V, B' ≤ A' →
      finrank F A' - finrank F B' < finrank F A - finrank F B → bl_P pr B' A') :
    bl_P pr B A := by
  intro s hs hC p hp a hsupp
  by_cases hAB : B = A
  · subst hAB; exact bl_same pr s hs B p hp a hsupp
  have hcase1 : ∀ s' : ι → ℝ, (∀ i, 0 ≤ s' i) → bl_C pr s' B A → ∀ W : Submodule F V,
      B ≤ W → W ≤ A → W ≠ B → W ≠ A → bl_d B W = ∑ i, s' i * bl_e pr B W i →
      bl_G pr s' B p :=
    fun s' hs' hC' W h1 h2 h3 h4 h5 => bl_case1 pr B A IHn s' hs' hC' W h1 h2 h3 h4 h5 p hp a hsupp
  suffices H : ∀ K, ∀ s' : ι → ℝ, (∀ i, 0 ≤ s' i) → bl_C pr s' B A →
      (univ.filter fun i => s' i ≠ 0).card = K → bl_G pr s' B p from H _ s hs hC rfl
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro s' hs' hC' hK
    have hIHk : ∀ s'' : ι → ℝ, (∀ i, 0 ≤ s'' i) → bl_C pr s'' B A →
        (univ.filter fun i => s'' i ≠ 0).card < K → bl_G pr s'' B p :=
      fun s'' h1 h2 h3 => ih _ h3 s'' h1 h2 rfl
    have hAt : ∀ s'' : ι → ℝ, (∀ i, 0 ≤ s'' i) → bl_C pr s'' B A →
        (univ.filter fun i => s'' i ≠ 0).card ≤ K → bl_d B A = ∑ i, s'' i * bl_e pr B A i →
        bl_G pr s'' B p :=
      fun s'' h1 h2 h3 h4 => bl_tight pr B A hBA hAB p hp a hsupp K hIHk hcase1 s'' h1 h2 h3 h4
    by_cases hA : bl_d B A = ∑ i, s' i * bl_e pr B A i
    · exact hAt s' hs' hC' hK.le hA
    · exact bl_nontight pr B A hBA hAB p hp K hIHk hcase1 hAt s' hs' hC' hK.le hA

theorem bl_all (pr : ι → V →ₗ[F] Y) (n : ℕ) : ∀ B A : Submodule F V, B ≤ A →
    finrank F A - finrank F B = n → bl_P pr B A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B A hBA hn
    exact bl_step pr B A hBA fun B' A' h h' => ih _ (hn ▸ h') B' A' h rfl

end BL

/-- Entropic Brascamp–Lieb inequality over a finite field, for the section `A/B`
(`B ≤ A`), and weights `p` supported on a coset `a + A`. -/
theorem bl {F : Type} [Field F] [Fintype F] {V Y ι : Type} [AddCommGroup V] [Module F V]
    [Fintype V] [AddCommGroup Y] [Module F Y] [Fintype ι]
    (pr : ι → V →ₗ[F] Y) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    (B A : Submodule F V) (hBA : B ≤ A)
    (hcond : ∀ W : Submodule F V, B ≤ W → W ≤ A →
      (finrank F W : ℝ) - finrank F B ≤
        ∑ i, s i * ((finrank F (W.map (pr i)) : ℝ) - finrank F (B.map (pr i))))
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (a : V) (hsupp : ∀ v, p v ≠ 0 → v - a ∈ A) :
    ent p B.mkQ ≤ ∑ i, s i * ent p (fun v => (B.map (pr i)).mkQ (pr i v)) := by
  exact bl_all pr _ B A hBA rfl s hs hcond p hp a hsupp

end SubspaceEvasion312.Explicit.Dev.DLR
end
end

section
set_option autoImplicit false
noncomputable section
open Real Finset Module

namespace SubspaceEvasion312.Explicit.Dev.DLR

/-- The final real-number estimate. -/
theorem final_real {N m τ ε ℓ R : ℝ} (hN : 1 ≤ N) (hm : 0 < m) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (hℓ : 1 ≤ ℓ) (hR1 : (τ + ε) * m * N ≤ R) (hR2 : R ≤ m * N)
    (hmain : (1 - τ) * m * N * log N ≤ (m * N - R) * log N + R * log (m * (ℓ * N) / R)) :
    log N ≤ (τ + ε) / ε * log (ℓ / (τ + ε)) := by
  set δ := τ + ε with hδ
  have hδpos : 0 < δ := by linarith
  have hmN : 0 < m * N := by positivity
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR1
  set x := R / (m * N) with hx
  have hx1 : δ ≤ x := by rw [hx, le_div_iff₀ hmN]; linarith
  have hx2 : x ≤ 1 := by rw [hx, div_le_iff₀ hmN]; linarith
  have hxpos : 0 < x := by linarith
  have e1 : m * (ℓ * N) / R = ℓ / x := by rw [hx]; field_simp
  have e2 : R = x * (m * N) := by rw [hx]; field_simp
  set L := log N
  set Lx := log (ℓ / x)
  have h3 : (m * N) * ((x - τ) * L) ≤ (m * N) * (x * Lx) := by
    rw [e1, e2] at hmain
    nlinarith [hmain]
  have h4 : (x - τ) * L ≤ x * Lx := le_of_mul_le_mul_left h3 hmN
  have hL : 0 ≤ L := log_nonneg hN
  have hLx : 0 ≤ Lx := log_nonneg (by rw [le_div_iff₀ hxpos]; linarith)
  have hLmono : Lx ≤ log (ℓ / δ) :=
    log_le_log (by positivity) (div_le_div_of_nonneg_left (by linarith) hδpos hx1)
  have hcross : ε * x ≤ δ * (x - τ) := by rw [hδ]; nlinarith
  have hxτ : 0 < x - τ := by linarith
  have a := mul_le_mul_of_nonneg_left h4 hε.le
  have b := mul_le_mul_of_nonneg_right hcross hLx
  have c := mul_le_mul_of_nonneg_left hLmono (mul_nonneg hδpos.le hxτ.le)
  have h5 : (x - τ) * (ε * L) ≤ (x - τ) * (δ * log (ℓ / δ)) := by nlinarith [a, b, c]
  have h6 : ε * L ≤ δ * log (ℓ / δ) := le_of_mul_le_mul_left h5 hxτ
  rw [div_mul_eq_mul_div, le_div_iff₀ hε]
  linarith

theorem coord_rank_nullity {F : Type} [Field F] {s m : ℕ} (W : Submodule F (Blocks F s m))
    (i : Fin m) :
    (finrank F (coordinateKernel W i) : ℝ) +
      finrank F (W.map (LinearMap.proj i : Blocks F s m →ₗ[F] Vec F s)) = finrank F W := by
  set f := (LinearMap.proj i : Blocks F s m →ₗ[F] Vec F s).domRestrict W
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : LinearMap.range f = W.map (LinearMap.proj i) := LinearMap.range_domRestrict _ _
  have h3 : coordinateKernel W i = (LinearMap.ker f).map W.subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxW, hx0⟩ := hx
      exact ⟨⟨x, hxW⟩, by simpa [f] using hx0, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa [f] using hy⟩
  rw [h3, Submodule.finrank_map_subtype_eq, ← h2, add_comm]
  exact_mod_cast h1

theorem design_cond {F : Type} [Field F] {s m r : ℕ} (hm : 0 < m) (C : Code F s m)
    (τ : ℕ → ℝ) (hC : SubspaceDesign C τ) (U : Submodule F (Blocks F s m))
    (hU : finrank F U ≤ r) (W : Submodule F (Blocks F s m)) (hWC : W ≤ C) (hWU : W ≤ U) :
    (1 - τ r) * m * finrank F W ≤
      ∑ i, (finrank F (W.map (LinearMap.proj i : Blocks F s m →ₗ[F] Vec F s)) : ℝ) := by
  have hd := hC.2 r W hWC ((Submodule.finrank_mono hWU).trans hU)
  rw [div_le_iff₀ (by exact_mod_cast hm)] at hd
  have hrn : ∀ i, (finrank F (W.map (LinearMap.proj i : Blocks F s m →ₗ[F] Vec F s)) : ℝ) =
      finrank F W - finrank F (coordinateKernel W i) := fun i => by
    linarith [coord_rank_nullity W i]
  simp_rw [hrn]
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

theorem hamming_eq {F : Type} {s m : ℕ} (c y : Blocks F s m) :
    ∃ X : Finset (Fin m), hamming c y = X.card ∧ ∀ i, i ∉ X → c i = y i := by
  unfold hamming
  exact ⟨_, rfl, fun i hi => by simpa using hi⟩

theorem agree_ge {F : Type} [Field F] {s m : ℕ} (S : Fin m → Finset (Vec F s))
    (c y : Blocks F s m) (hy : ∀ i, y i ∈ S i) (Q : Finset (Fin m))
    (hQ : ∀ i, c i ∈ S i → i ∈ Q) : (m : ℝ) - hamming c y ≤ Q.card := by
  obtain ⟨X, hX, hXc⟩ := hamming_eq c y
  rw [hX]
  have hsub : univ \ X ⊆ Q := fun i hi => hQ i (by
    rw [hXc i (mem_sdiff.1 hi).2]; exact hy i)
  have h1 := card_sdiff_add_card_eq_card (subset_univ X)
  rw [card_univ, Fintype.card_fin] at h1
  have h2 : ((univ \ X).card : ℝ) ≤ Q.card := by exact_mod_cast card_le_card hsub
  have h3 : ((univ \ X).card : ℝ) + X.card = m := by exact_mod_cast h1
  linarith

theorem dlr {F : Type} [Field F] [Fintype F]
    {s m r ℓ : ℕ} (hm : 0 < m) (C : Code F s m) (τ : ℕ → ℝ)
    (hC : SubspaceDesign C τ) (ε : ℝ) (hε : 0 < ε) (hden : 0 < τ r + ε) :
    ListRecoverable C r (1 - τ r - ε) ℓ
      (ENNReal.ofReal (((ℓ : ℝ) / (τ r + ε)) ^ ((τ r + ε) / ε))) := by
  classical
  intro U hU S hS T hT
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  set δ := τ r + ε with hδ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rcases T.eq_empty_or_nonempty with hTe | ⟨c0, hc0⟩
  · rw [hTe, card_empty, Nat.cast_zero]
    exact rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hden.le) _
  obtain ⟨-, -, y0, hy0, hh0⟩ := hT hc0
  have hρ : 0 ≤ 1 - τ r - ε := by
    have : (0 : ℝ) ≤ (1 - τ r - ε) * m := le_trans (Nat.cast_nonneg _) hh0
    by_contra hneg
    push Not at hneg
    nlinarith
  have hℓ : (1 : ℝ) ≤ ℓ := by
    have := card_pos.2 ⟨_, hy0 ⟨0, hm⟩⟩
    exact_mod_cast this.trans_le (hS _)
  have hbase : 1 ≤ (ℓ : ℝ) / δ := by rw [le_div_iff₀ hden]; linarith
  have hB1 : 1 ≤ ((ℓ : ℝ) / δ) ^ (δ / ε) := one_le_rpow hbase (by positivity)
  by_cases hnz : ∃ c ∈ T, c ≠ 0
  swap
  · push Not at hnz
    have : T.card ≤ 1 := card_le_one.2 fun a ha b hb => by rw [hnz a ha, hnz b hb]
    calc (T.card : ℝ) ≤ 1 := by exact_mod_cast this
      _ ≤ _ := hB1
  obtain ⟨c, hcT, hc⟩ := hnz
  have hcCU := hT hcT
  have hτ : 0 ≤ τ r := by
    have hle : (F ∙ c) ≤ U := (Submodule.span_singleton_le_iff_mem _ _).2 hcCU.2.1
    have hsp : finrank F (F ∙ c) ≤ r := (Submodule.finrank_mono hle).trans hU
    have := hC.2 r (F ∙ c) ((Submodule.span_singleton_le_iff_mem _ _).2 hcCU.1) hsp
    rw [finrank_span_singleton hc] at this
    have h0 : 0 ≤ (∑ i : Fin m, (finrank F (coordinateKernel (F ∙ c) i) : ℝ)) / m := by
      positivity
    simp only [Nat.cast_one, one_mul] at this
    linarith
  set A : Submodule F (Blocks F s m) := C ⊓ U with hA
  set α := (1 - τ r) * m with hα
  have hαpos : 0 < α := by
    have : 0 < 1 - τ r := by linarith
    positivity
  set p : Blocks F s m → ℝ := fun v => if v ∈ T then 1 else 0 with hp
  have hpnn : ∀ v, 0 ≤ p v := fun v => by simp only [hp]; split_ifs <;> norm_num
  have hcond : ∀ W : Submodule F (Blocks F s m), ⊥ ≤ W → W ≤ A →
      (finrank F W : ℝ) - finrank F (⊥ : Submodule F (Blocks F s m)) ≤
        ∑ i : Fin m, (fun _ => 1 / α) i *
          ((finrank F (W.map (LinearMap.proj i : Blocks F s m →ₗ[F] Vec F s)) : ℝ) -
            finrank F ((⊥ : Submodule F (Blocks F s m)).map
              (LinearMap.proj i : Blocks F s m →ₗ[F] Vec F s))) := by
    intro W _ hW
    have h0 : ∀ i : Fin m, (finrank F ((⊥ : Submodule F (Blocks F s m)).map
        (LinearMap.proj i : Blocks F s m →ₗ[F] Vec F s)) : ℝ) = 0 := fun i => by
      rw [Submodule.map_bot]; simp
    simp only [h0, finrank_bot, Nat.cast_zero, sub_zero, ← mul_sum]
    have := design_cond hm C τ hC U hU W (hW.trans inf_le_left) (hW.trans inf_le_right)
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hαpos, hα]
    linarith
  have hsupp : ∀ v, p v ≠ 0 → v - 0 ∈ A := fun v hv => by
    have hvT : v ∈ T := by
      by_contra h
      simp [hp, h] at hv
    obtain ⟨h1, h2, -⟩ := hT hvT
    rw [sub_zero]
    exact ⟨h1, h2⟩
  have hbl := bl (fun i : Fin m => (LinearMap.proj i : Blocks F s m →ₗ[F] Vec F s))
    (fun _ => 1 / α) (fun _ => by positivity) ⊥ A bot_le hcond p hpnn 0 hsupp
  have hL : ent p (⊥ : Submodule F (Blocks F s m)).mkQ = T.card * log T.card := by
    rw [ent_congr p _ id (fun v w _ _ => by simp [Submodule.Quotient.eq, sub_eq_zero])]
    exact ent_indicator T
  have hR : ∀ i : Fin m, ent p (fun v => ((⊥ : Submodule F (Blocks F s m)).map
      (LinearMap.proj i : Blocks F s m →ₗ[F] Vec F s)).mkQ
        ((LinearMap.proj i : Blocks F s m →ₗ[F] Vec F s) v)) = ent p (fun v => v i) :=
    fun i => ent_congr _ _ _ (fun v w _ _ => by simp [Submodule.Quotient.eq, sub_eq_zero])
  rw [hL] at hbl
  simp only [hR] at hbl
  set N := T.card with hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast card_pos.2 ⟨c, hcT⟩
  have hE : α * (N * log N) ≤ ∑ i : Fin m, ent p (fun v => v i) := by
    rw [← mul_sum, one_div] at hbl
    calc α * (N * log N) ≤ α * (α⁻¹ * ∑ i : Fin m, ent p (fun v => v i)) :=
          mul_le_mul_of_nonneg_left hbl hαpos.le
      _ = _ := by field_simp
  set n : Fin m → ℕ := fun i => (T.filter (fun v => v i ∈ S i)).card with hn
  have hsplit : ∀ i, ent p (fun v => v i) ≤
      ((N : ℝ) - n i) * log N + (n i : ℝ) * log ((ℓ : ℝ) * N / n i) :=
    fun i => ent_split_bound T (fun v => v i) (S i) ℓ (hS i)
  set R : ℝ := ∑ i, (n i : ℝ) with hRdef
  have hRle : R ≤ m * N := by
    calc R ≤ ∑ _i : Fin m, (N : ℝ) :=
          sum_le_sum fun i _ => by exact_mod_cast card_filter_le _ _
      _ = m * N := by simp
  have hRge : δ * m * N ≤ R := by
    have hni : ∀ i, (n i : ℝ) = ∑ v ∈ T, if v i ∈ S i then (1 : ℝ) else 0 := fun i => by
      simp only [hn]
      rw [Finset.natCast_card_filter]
    have hRs : R = ∑ v ∈ T, (((univ : Finset (Fin m)).filter (fun i => v i ∈ S i)).card : ℝ) := by
      rw [hRdef]
      simp_rw [hni]
      rw [sum_comm]
      refine sum_congr rfl fun v _ => ?_
      rw [Finset.natCast_card_filter]
    rw [hRs]
    calc δ * m * N = ∑ _v ∈ T, δ * m := by simp [hN]; ring
      _ ≤ _ := sum_le_sum fun v hv => by
        obtain ⟨-, -, y, hy, hh⟩ := hT hv
        have := agree_ge S v y hy _ (fun i hi => mem_filter.2 ⟨mem_univ i, hi⟩)
        rw [hδ]
        nlinarith
  have hlogsum := logsum univ (fun i => (n i : ℝ)) (fun _ => (ℓ : ℝ) * N)
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => by positivity) (fun _ _ _ => by positivity)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hlogsum
  have hmain : (1 - τ r) * m * N * log N ≤
      (m * N - R) * log N + R * log (m * (ℓ * N) / R) := by
    have hs := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin m))) => hsplit i
    rw [sum_add_distrib, ← sum_mul, sum_sub_distrib] at hs
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    rw [← hRdef] at hs hlogsum
    have : α * (N * log N) = (1 - τ r) * m * N * log N := by rw [hα]; ring
    linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast card_pos.2 ⟨c, hcT⟩
  have hlogN := final_real hN1 hmR hτ hε hℓ hRge hRle hmain
  calc (N : ℝ) = exp (log N) := (exp_log hNpos).symm
    _ ≤ exp (log ((ℓ : ℝ) / δ) * (δ / ε)) := exp_le_exp.2 (by rw [mul_comm]; exact hlogN)
    _ = _ := (rpow_def_of_pos (by positivity) _).symm

end SubspaceEvasion312.Explicit.Dev.DLR

namespace SubspaceEvasion312.Explicit
open scoped ENNReal
theorem chk_design_list_recovery {F : Type} [Field F] [Fintype F]
    {s m r ℓ : ℕ} (hm : 0 < m) (C : Code F s m) (τ : ℕ → ℝ)
    (hC : SubspaceDesign C τ) (ε : ℝ) (hε : 0 < ε) (hden : 0 < τ r + ε) :
    ListRecoverable C r (1 - τ r - ε) ℓ
      (ENNReal.ofReal (((ℓ : ℝ) / (τ r + ε)) ^ ((τ r + ε) / ε))) := by
  exact Dev.DLR.dlr hm C τ hC ε hε hden
end SubspaceEvasion312.Explicit
end
end

theorem solution : type_of% @SubspaceEvasion312.Explicit.chk_design_list_recovery := @SubspaceEvasion312.Explicit.chk_design_list_recovery
