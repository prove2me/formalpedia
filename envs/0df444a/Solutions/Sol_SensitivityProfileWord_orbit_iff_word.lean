-- Prove2me | solution 1 for SensitivityProfileWord.orbit_iff_word
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-10-21T22:42:17.018443+00:00
-- url     : https://prove2.me/submissions/657e868f-70ea-4d5e-b7ce-5f84764f2423

import Definitions.Def_SensitivityProfileWord


/-! Homogeneity follows the corresponding proofs in accepted Prove2Me
submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a, by yousofy with Codex,
retaining the upstream attribution. Monotonicity is proved below directly.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.all false
namespace ProfileOrbitLemmas
open SensitivityProfileCycle SensitivityProfileSearch
variable {n : ℕ}

theorem targetCost_mul (q v a b u : ℕ) :
    targetCost q v (a*u) (b*u) = targetCost q v a b*u := by
  simp only [targetCost, Nat.add_mul, Nat.mul_assoc]

theorem coupledCost_mul (q v a b c e u : ℕ) :
    coupledCost q v (a*u) (b*u) (c*u) (e*u) = coupledCost q v a b c e*u := by
  unfold coupledCost
  rw [Finset.sup_mul₀]
  congr 1
  funext n
  rw [Finset.sup_mul₀]
  congr 1
  funext m
  split_ifs <;> simp only [Nat.zero_mul, Nat.add_mul, Nat.mul_assoc]

theorem ordinaryCost_mul (q v a b c e w : ℕ) :
    ordinaryCost q v (a*w) (b*w) (c*w) (e*w) =
      ordinaryCost q v a b c e*w := by
  unfold ordinaryCost
  rw [Finset.sup_mul₀]
  congr 1
  funext n
  rw [Finset.sup_mul₀]
  congr 1
  funext m
  rw [Finset.sup_mul₀]
  congr 1
  funext u
  split_ifs <;> simp only [Nat.zero_mul, Nat.add_mul, Nat.mul_assoc]

theorem sourceCost_mul (v w a b c e s : ℕ) :
    sourceCost v w (a*s) (b*s) (c*s) (e*s) = sourceCost v w a b c e*s := by
  unfold sourceCost
  rw [Finset.sup_mul₀]
  congr 1
  funext n
  rw [Finset.sup_mul₀]
  congr 1
  funext m
  rw [Finset.sup_mul₀]
  congr 1
  funext u
  split_ifs <;> simp only [Nat.zero_mul, Nat.add_mul, Nat.mul_assoc]

theorem strictSourceCost_mul (t w a b c e s : ℕ) :
    strictSourceCost t w (a*s) (b*s) (c*s) (e*s) =
      strictSourceCost t w a b c e*s := by
  simp only [strictSourceCost, Nat.add_mul, Nat.mul_assoc, max_mul]

theorem dedupCost_mul (internal : ℕ → ℕ) (q v a b c e w : ℕ) :
    dedupCost internal q v (a*w) (b*w) (c*w) (e*w) =
      dedupCost internal q v a b c e*w := by
  unfold dedupCost
  rw [Finset.sup_mul₀]
  congr 1
  funext n
  rw [Finset.sup_mul₀]
  congr 1
  funext m
  rw [Finset.sup_mul₀]
  congr 1
  funext u
  split_ifs <;> simp only [Nat.zero_mul, Nat.add_mul, Nat.mul_assoc]

theorem rawOne_mul (h : ℕ) (C : Recipe n) (Z Y : Fin n → Fin n → ℕ) (u : ℕ) (i j : Fin n) :
    rawOne h C (fun i j => Z i j*u) (fun i j => Y i j*u) i j = rawOne h C Z Y i j*u := by
  simp only [rawOne]
  split_ifs <;> simp only [Nat.add_mul, Nat.mul_assoc, Nat.zero_mul]

theorem rawZeroCoupled_mul (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (u : ℕ) (i j : Fin n) :
    rawZeroCoupled k t v C (fun i j => Z i j*u) (fun i j => Y i j*u) i j = rawZeroCoupled k t v C Z Y i j*u := by
  simp only [rawZeroCoupled]
  split_ifs <;> first | rfl | simp only [Nat.add_mul, Nat.mul_assoc, max_mul, Nat.zero_mul, ← min_mul, targetCost_mul, coupledCost_mul]

theorem rawZeroOrdinary_mul (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (w : ℕ) (i j : Fin n) :
    rawZeroOrdinary k t v C (fun i j => Z i j*w) (fun i j => Y i j*w) i j =
      rawZeroOrdinary k t v C Z Y i j*w := by
  unfold rawZeroOrdinary
  split_ifs <;> simp only [rawZeroCoupled_mul,
    ordinaryCost_mul, min_mul]

theorem rawZeroSource_mul (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (s : ℕ) (i j : Fin n) :
    rawZeroSource k t v w C (fun i j => Z i j*s) (fun i j => Y i j*s) i j =
      rawZeroSource k t v w C Z Y i j*s := by
  unfold rawZeroSource
  split_ifs <;> simp only [rawZeroOrdinary_mul,
    sourceCost_mul, min_mul]

theorem rawZeroSourceFull_mul (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (s : ℕ) (i j : Fin n) :
    rawZeroSourceFull k t v w C (fun i j => Z i j*s) (fun i j => Y i j*s) i j =
      rawZeroSourceFull k t v w C Z Y i j*s := by
  unfold rawZeroSourceFull
  split_ifs <;> simp only [rawZeroSource_mul, strictSourceCost_mul,
    Nat.add_mul, Nat.mul_assoc, max_mul, min_mul]

theorem rawZeroDedupBoth_mul (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (w : ℕ) (i j : Fin n) :
    rawZeroDedupBoth k t v C (fun i j => Z i j*w) (fun i j => Y i j*w) i j =
      rawZeroDedupBoth k t v C Z Y i j*w := by
  unfold rawZeroDedupBoth
  split_ifs <;> simp only [rawZeroCoupled_mul,
    ordinaryDedupInternalCost, dedupCost_mul, min_mul]

theorem rawZeroSourceCombined_mul (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (s : ℕ) (i j : Fin n) :
    rawZeroSourceCombined k t v w C (fun i j => Z i j*s) (fun i j => Y i j*s) i j =
      rawZeroSourceCombined k t v w C Z Y i j*s := by
  simp only [rawZeroSourceCombined, rawZeroSourceFull_mul, rawZeroDedupBoth_mul, min_mul]

@[gcongr] theorem targetCost_mono (q v a b a' b' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') :
    targetCost q v a b ≤ targetCost q v a' b' := by
  unfold targetCost
  gcongr

@[gcongr] theorem coupledCost_mono (q v a b c e a' b' c' e' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (he : e ≤ e') :
    coupledCost q v a b c e ≤ coupledCost q v a' b' c' e' := by
  unfold coupledCost
  apply Finset.sup_mono_fun
  intro x hx
  apply Finset.sup_mono_fun
  intro y hy
  split_ifs <;> gcongr

@[gcongr] theorem ordinaryCost_mono (q v a b c e a' b' c' e' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (he : e ≤ e') :
    ordinaryCost q v a b c e ≤ ordinaryCost q v a' b' c' e' := by
  unfold ordinaryCost
  apply Finset.sup_mono_fun
  intro x hx
  apply Finset.sup_mono_fun
  intro y hy
  apply Finset.sup_mono_fun
  intro z hz
  split_ifs <;> gcongr

@[gcongr] theorem sourceCost_mono (v w a b c e a' b' c' e' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (he : e ≤ e') :
    sourceCost v w a b c e ≤ sourceCost v w a' b' c' e' := by
  unfold sourceCost
  apply Finset.sup_mono_fun
  intro x hx
  apply Finset.sup_mono_fun
  intro y hy
  apply Finset.sup_mono_fun
  intro z hz
  split_ifs <;> gcongr

@[gcongr] theorem strictSourceCost_mono (t w a b c e a' b' c' e' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (he : e ≤ e') :
    strictSourceCost t w a b c e ≤ strictSourceCost t w a' b' c' e' := by
  unfold strictSourceCost
  gcongr

@[gcongr] theorem dedupCost_mono (internal : ℕ → ℕ) (q v a b c e a' b' c' e' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (he : e ≤ e') :
    dedupCost internal q v a b c e ≤ dedupCost internal q v a' b' c' e' := by
  unfold dedupCost
  apply Finset.sup_mono_fun
  intro x hx
  apply Finset.sup_mono_fun
  intro y hy
  apply Finset.sup_mono_fun
  intro z hz
  split_ifs <;> gcongr

@[gcongr] theorem ordinaryDedupInternalCost_mono (r q v a b c e a' b' c' e' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (he : e ≤ e') :
    ordinaryDedupInternalCost r q v a b c e ≤ ordinaryDedupInternalCost r q v a' b' c' e' := by
  unfold ordinaryDedupInternalCost
  gcongr

@[gcongr] theorem rawOne_mono (h : ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawOne h C Z Y i j ≤ rawOne h C Z' Y' i j := by
  unfold rawOne
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

@[gcongr] theorem rawZeroCoupled_mono (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawZeroCoupled k t v C Z Y i j ≤ rawZeroCoupled k t v C Z' Y' i j := by
  unfold rawZeroCoupled
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

@[gcongr] theorem rawZeroOrdinary_mono (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawZeroOrdinary k t v C Z Y i j ≤ rawZeroOrdinary k t v C Z' Y' i j := by
  unfold rawZeroOrdinary
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

@[gcongr] theorem rawZeroSource_mono (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawZeroSource k t v w C Z Y i j ≤ rawZeroSource k t v w C Z' Y' i j := by
  unfold rawZeroSource
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

@[gcongr] theorem rawZeroSourceFull_mono (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawZeroSourceFull k t v w C Z Y i j ≤ rawZeroSourceFull k t v w C Z' Y' i j := by
  unfold rawZeroSourceFull
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

@[gcongr] theorem rawZeroDedupBoth_mono (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawZeroDedupBoth k t v C Z Y i j ≤ rawZeroDedupBoth k t v C Z' Y' i j := by
  unfold rawZeroDedupBoth
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

@[gcongr] theorem rawZeroSourceCombined_mono (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y Z' Y' : Fin n → Fin n → ℕ)
    (hZ : ∀ i j, Z i j ≤ Z' i j) (hY : ∀ i j, Y i j ≤ Y' i j)
    (i j : Fin n) :
    rawZeroSourceCombined k t v w C Z Y i j ≤ rawZeroSourceCombined k t v w C Z' Y' i j := by
  unfold rawZeroSourceCombined
  try dsimp only
  try split_ifs
  all_goals gcongr <;> first | exact hZ _ _ | exact hY _ _ | exact hZ | exact hY

end ProfileOrbitLemmas

namespace SensitivityProfileWord
open ProfileOrbitLemmas
open SensitivityProfileCycle SensitivityProfileSearch
variable {n : ℕ}

def ProfileLE (P Q : Profile n) : Prop :=
  ∀ i j, P.zero i j ≤ Q.zero i j ∧ P.one i j ≤ Q.one i j

def scale (P : Profile n) (u : ℕ) : Profile n :=
  ⟨fun i j => P.zero i j*u, fun i j => P.one i j*u⟩

theorem envelope_mono (A B : Matrix n) (h : ∀ i j, A i j ≤ B i j)
    (i j : Fin n) : envelope A i j ≤ envelope B i j := by
  unfold envelope
  split_ifs with hij
  · exact Finset.inf'_mono_fun (fun ab _ => h ab.1 ab.2)
  · exact le_rfl

theorem envelope_mul (A : Matrix n) (u : ℕ) (i j : Fin n) :
    envelope (fun a b => A a b*u) i j = envelope A i j*u := by
  unfold envelope
  split_ifs with hij
  · let S := intervals i j
    let hs := intervals_nonempty hij
    obtain ⟨ab, hab, heq⟩ := Finset.exists_mem_eq_inf' hs (fun ab => A ab.1 ab.2)
    apply le_antisymm
    · calc
        S.inf' hs (fun ab => A ab.1 ab.2*u) ≤ A ab.1 ab.2*u :=
          Finset.inf'_le _ hab
        _ = S.inf' hs (fun ab => A ab.1 ab.2)*u := by rw [heq]
    · apply Finset.le_inf'
      intro cd hcd
      exact Nat.mul_le_mul_right u (Finset.inf'_le _ hcd)
  · exact (Nat.zero_mul u).symm

theorem envelope_le (A : Matrix n) (i j : Fin n) :
    envelope A i j ≤ A i j := by
  unfold envelope
  split_ifs with hij
  · exact Finset.inf'_le (b := (i,j)) _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hij, le_rfl⟩)
  · exact Nat.zero_le _

theorem envelope_interval (A : Matrix n) (i j a b : Fin n)
    (hia : i ≤ a) (hab : a ≤ b) (hbj : b ≤ j) :
    envelope A i j ≤ envelope A a b := by
  have hij : i ≤ j := hia.trans (hab.trans hbj)
  simp only [envelope, dif_pos hij, dif_pos hab]
  apply Finset.le_inf'
  intro cd hcd
  have hcd' := (Finset.mem_filter.mp hcd).2
  apply Finset.inf'_le
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hia.trans hcd'.1, hcd'.2.1, hcd'.2.2.trans hbj⟩

theorem envelope_idempotent (A : Matrix n) : envelope (envelope A) = envelope A := by
  funext i j
  apply le_antisymm (envelope_le (envelope A) i j)
  unfold envelope at ⊢
  split_ifs with hij
  · apply Finset.le_inf'
    intro ab hab
    have hab' := (Finset.mem_filter.mp hab).2
    simpa only [envelope, dif_pos hij] using
      envelope_interval A i j ab.1 ab.2 hab'.1 hab'.2.1 hab'.2.2
  · exact le_rfl

theorem normalize_idempotent (P : Profile n) : normalize (normalize P) = normalize P := by
  simp only [SensitivityProfileSearch.normalize, envelope_idempotent]

theorem normalize_step (C : Recipe n) (P : Profile n) :
    normalize (step C P) = step C P := by
  simp only [SensitivityProfileSearch.normalize, step, envelope_idempotent]

theorem normalize_mono (P Q : Profile n) (h : ProfileLE P Q) :
    ProfileLE (normalize P) (normalize Q) := by
  intro i j
  exact ⟨envelope_mono P.zero Q.zero (fun a b => (h a b).1) i j,
    envelope_mono P.one Q.one (fun a b => (h a b).2) i j⟩

theorem normalize_mul (P : Profile n) (u : ℕ) :
    normalize (scale P u) = scale (normalize P) u := by
  simp only [SensitivityProfileSearch.normalize, scale]
  congr 1 <;> funext i j <;> exact envelope_mul _ u i j

theorem step_mono (C : Recipe n) (P Q : Profile n) (h : ProfileLE P Q) :
    ProfileLE (step C P) (step C Q) := by
  intro i j
  constructor
  · apply envelope_mono
    intro a b
    exact rawZeroSourceCombined_mono _ _ _ _ C _ _ _ _
      (fun x y => (h x y).1) (fun x y => (h x y).2) a b
  · apply envelope_mono
    intro a b
    exact rawOne_mono _ C _ _ _ _
      (fun x y => (h x y).1) (fun x y => (h x y).2) a b

theorem step_mul (C : Recipe n) (P : Profile n) (u : ℕ) :
    step C (scale P u) = scale (step C P) u := by
  simp only [step, scale]
  congr 1
  · have hraw := funext (fun i => funext (fun j =>
      rawZeroSourceCombined_mul 14055 24 (extendCutoffs cutoffs) 22 C P.zero P.one u i j))
    rw [hraw]
    funext i j
    exact envelope_mul _ u i j
  · have hraw := funext (fun i => funext (fun j => rawOne_mul 7027 C P.zero P.one u i j))
    rw [hraw]
    funext i j
    exact envelope_mul _ u i j

theorem orbit_mono {p : ℕ} (recipes : Fin (p+1) → Recipe n)
    (P Q : Profile n) (h : ProfileLE P Q) (d : ℕ) :
    ProfileLE (orbit recipes P d) (orbit recipes Q d) := by
  induction d with
  | zero => exact normalize_mono P Q h
  | succ d ih => exact step_mono _ _ _ ih

theorem orbit_mul {p : ℕ} (recipes : Fin (p+1) → Recipe n)
    (P : Profile n) (u d : ℕ) :
    orbit recipes (scale P u) d = scale (orbit recipes P d) u := by
  induction d with
  | zero => exact normalize_mul P u
  | succ d ih => simp only [orbit, ih, step_mul]

theorem orbit_normalize {p : ℕ} (recipes : Fin (p+1) → Recipe n)
    (P : Profile n) (d : ℕ) :
    orbit recipes (normalize P) d = orbit recipes P d := by
  induction d with
  | zero => exact normalize_idempotent P
  | succ d ih => simp only [orbit, ih]

end SensitivityProfileWord


set_option autoImplicit false
namespace SensitivityProfileWord

/-- A strict integral power gap absorbs every fixed multiplicative overhead. -/
theorem exists_absorbing_power (C R G : ℕ) (hR : 0 < R)
    (hgap : R^43 < G^20) :
    ∃ m : ℕ, 0 < m ∧ (C * R^m)^43 < (G^m)^20 := by
  have ha : (0 : ℚ) < (R : ℚ)^43 := pow_pos (by exact_mod_cast hR) _
  have hg : (1 : ℚ) < (G : ℚ)^20 / (R : ℚ)^43 := by
    apply (one_lt_div ha).2
    exact_mod_cast hgap
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((C : ℚ)^43) hg
  have hm' : (C : ℚ)^43 < ((G : ℚ)^20 / (R : ℚ)^43)^(m+1) :=
    hm.trans (pow_lt_pow_right₀ hg (Nat.lt_succ_self m))
  have hh : (C : ℚ)^43 * ((R : ℚ)^43)^(m+1) <
      ((G : ℚ)^20)^(m+1) := by
    apply (lt_div_iff₀ (pow_pos ha _)).mp
    simpa only [div_pow] using hm'
  refine ⟨m+1, Nat.zero_lt_succ m, ?_⟩
  have hh' : ((C * R^(m+1)) : ℚ)^43 < ((G : ℚ)^(m+1))^20 := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm] using hh
  exact_mod_cast hh'

end SensitivityProfileWord

namespace SensitivityProfileWord
open SensitivityProfileCycle SensitivityProfileSearch
variable {n : ℕ}

theorem profileLE_trans {P Q S : Profile n} (hPQ : ProfileLE P Q)
    (hQS : ProfileLE Q S) : ProfileLE P S := by
  intro i j
  exact ⟨(hPQ i j).1.trans (hQS i j).1, (hPQ i j).2.trans (hQS i j).2⟩

theorem scale_mono {P Q : Profile n} (hPQ : ProfileLE P Q) (u : ℕ) :
    ProfileLE (scale P u) (scale Q u) := by
  intro i j
  exact ⟨Nat.mul_le_mul_right u (hPQ i j).1, Nat.mul_le_mul_right u (hPQ i j).2⟩

theorem normalize_le (P : Profile n) : ProfileLE (normalize P) P := by
  intro i j
  exact ⟨envelope_le P.zero i j, envelope_le P.one i j⟩

theorem fold_mono (word : List (Recipe n)) (P Q : Profile n) (h : ProfileLE P Q) :
    ProfileLE (word.foldl (fun A C => step C A) P)
      (word.foldl (fun A C => step C A) Q) := by
  induction word generalizing P Q with
  | nil => exact h
  | cons C word ih => exact ih _ _ (step_mono C P Q h)

theorem fold_mul (word : List (Recipe n)) (P : Profile n) (u : ℕ) :
    word.foldl (fun A C => step C A) (scale P u) =
      scale (word.foldl (fun A C => step C A) P) u := by
  induction word generalizing P with
  | nil => rfl
  | cons C word ih => simp only [List.foldl_cons, step_mul, ih]

theorem normalize_fold (word : List (Recipe n)) (P : Profile n)
    (hP : normalize P = P) :
    normalize (word.foldl (fun A C => step C A) P) =
      word.foldl (fun A C => step C A) P := by
  induction word generalizing P with
  | nil => exact hP
  | cons C word ih => exact ih (step C P) (normalize_step C P)

theorem run_mono (word : List (Recipe n)) (P Q : Profile n) (h : ProfileLE P Q) :
    ProfileLE (run word P) (run word Q) :=
  fold_mono word _ _ (normalize_mono P Q h)

theorem run_mul (word : List (Recipe n)) (P : Profile n) (u : ℕ) :
    run word (scale P u) = scale (run word P) u := by
  unfold run
  rw [normalize_mul, fold_mul]

theorem normalize_run (word : List (Recipe n)) (P : Profile n) :
    normalize (run word P) = run word P :=
  normalize_fold word _ (normalize_idempotent P)

theorem run_append (word₁ word₂ : List (Recipe n)) (P : Profile n) :
    run (word₁ ++ word₂) P = run word₂ (run word₁ P) := by
  change (word₁ ++ word₂).foldl (fun A C => step C A) (normalize P) =
    word₂.foldl (fun A C => step C A) (normalize (run word₁ P))
  rw [normalize_run, List.foldl_append]
  rfl

theorem unitProfile_le (P : Profile n) (hP : PositiveUpper P) :
    ProfileLE (unitProfile n) P := by
  intro i j
  by_cases hij : i ≤ j
  · simpa only [unitProfile, if_pos hij] using hP i j hij
  · simp only [unitProfile, if_neg hij, Nat.zero_le, and_self]

theorem le_height (P : Profile n) (i j : Fin n) :
    P.zero i j ≤ height P ∧ P.one i j ≤ height P := by
  have h : max (P.zero i j) (P.one i j) ≤
      Finset.univ.sup (fun ij : Fin n × Fin n => max (P.zero ij.1 ij.2) (P.one ij.1 ij.2)) :=
    Finset.le_sup (f := fun ij : Fin n × Fin n =>
      max (P.zero ij.1 ij.2) (P.one ij.1 ij.2)) (Finset.mem_univ (i,j))
  exact ⟨(le_max_left _ _).trans (h.trans (le_max_right _ _)),
    (le_max_right _ _).trans (h.trans (le_max_right _ _))⟩

theorem height_le {P : Profile n} {B : ℕ} (hB : 2 ≤ B)
    (h : ∀ i j, P.zero i j ≤ B ∧ P.one i j ≤ B) : height P ≤ B := by
  apply max_le hB
  apply Finset.sup_le
  intro ij _
  exact max_le (h ij.1 ij.2).1 (h ij.1 ij.2).2

def repeatWord (word : List (Recipe n)) : ℕ → List (Recipe n)
  | 0 => []
  | m+1 => repeatWord word m ++ word

theorem repeatWord_length (word : List (Recipe n)) (m : ℕ) :
    (repeatWord word m).length = m * word.length := by
  induction m with
  | zero => simp only [repeatWord, List.length_nil, Nat.zero_mul]
  | succ m ih => simp only [repeatWord, List.length_append, ih, Nat.succ_mul]

theorem repeatWord_admissible {word : List (Recipe n)} (hword : Admissible word)
    (m : ℕ) : Admissible (repeatWord word m) := by
  induction m with
  | zero => intro C hC; cases hC
  | succ m ih =>
      intro C hC
      rcases List.mem_append.mp hC with hm | hw
      · exact ih C hm
      · exact hword C hw

theorem repeatWord_nonempty {word : List (Recipe n)} (hword : word ≠ [])
    {m : ℕ} (hm : 0 < m) : repeatWord word m ≠ [] := by
  apply List.length_pos_iff.mp
  rw [repeatWord_length]
  exact Nat.mul_pos hm (List.length_pos_iff.mpr hword)

theorem run_repeat_bound (word : List (Recipe n)) (P : Profile n) (R : ℕ)
    (hreturn : ProfileLE (run word P) (scale P R)) (m : ℕ) :
    ProfileLE (run (repeatWord word m) P) (scale P (R^m)) := by
  induction m with
  | zero => simpa only [repeatWord, run, List.foldl_nil, pow_zero, scale, Nat.mul_one] using normalize_le P
  | succ m ih =>
      rw [repeatWord, run_append]
      have h := run_mono word _ _ ih
      rw [run_mul] at h
      have hh := profileLE_trans h (scale_mono hreturn (R^m))
      simpa only [scale, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh

theorem height_run_repeat_unit_le (word : List (Recipe n)) (P : Profile n) (R : ℕ)
    (hR : 0 < R) (hP : PositiveUpper P)
    (hreturn : ProfileLE (run word P) (scale P R)) (m : ℕ) :
    height (run (repeatWord word m) (unitProfile n)) ≤ height P * R^m := by
  have hu := run_mono (repeatWord word m) _ _ (unitProfile_le P hP)
  have hb := profileLE_trans hu (run_repeat_bound word P R hreturn m)
  apply height_le
  · exact (le_max_left _ _).trans (Nat.le_mul_of_pos_right _ (pow_pos hR m))
  · intro i j
    exact ⟨(hb i j).1.trans (Nat.mul_le_mul_right _ (le_height P i j).1),
      (hb i j).2.trans (Nat.mul_le_mul_right _ (le_height P i j).2)⟩

/-- Every strict return certificate admits a finite recipe word starting from
the canonical unit profile. This removes all freely chosen profile matrices. -/
theorem word_crossing_of_return (word : List (Recipe n)) (P : Profile n) (R : ℕ)
    (hword : word ≠ []) (hadm : Admissible word) (hR : 1 < R)
    (hgap : R^43 < 14055^(20*word.length)) (hP : PositiveUpper P)
    (hreturn : ProfileLE (run word P) (scale P R)) :
    ∃ w : List (Recipe n), Crosses215 w := by
  have hgap' : R^43 < (14055^word.length)^20 := by
    simpa only [← pow_mul, Nat.mul_comm] using hgap
  obtain ⟨m, hm, hpow⟩ := exists_absorbing_power (height P) R
    (14055^word.length) (by omega) hgap'
  refine ⟨repeatWord word m, repeatWord_nonempty hword hm,
    repeatWord_admissible hadm m, ?_⟩
  have hh := height_run_repeat_unit_le word P R (by omega) hP hreturn m
  have hhpow : height (run (repeatWord word m) (unitProfile n))^43 ≤
      (height P * R^m)^43 := by gcongr
  have hfinal := hhpow.trans_lt hpow
  simpa only [repeatWord_length, ← pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hfinal

end SensitivityProfileWord


set_option autoImplicit false
namespace SensitivityProfileWord
open SensitivityProfileCycle SensitivityProfileSearch

theorem normalize_unit (n : ℕ) : normalize (unitProfile n) = unitProfile n := by
  have hval (i j : Fin n) :
      envelope (unitProfile n).zero i j = (unitProfile n).zero i j := by
    by_cases hij : i ≤ j
    · simp only [envelope, dif_pos hij]
      have hc : ∀ ab ∈ intervals i j, (unitProfile n).zero ab.1 ab.2 = 1 := by
        intro ab hab
        have hab' : ab.1 ≤ ab.2 := (Finset.mem_filter.mp hab).2.2.1
        simp [unitProfile, hab']
      rw [Finset.inf'_eq_of_forall (intervals_nonempty hij)
        (fun ab => (unitProfile n).zero ab.1 ab.2) hc]
      simp [unitProfile, hij]
    · simp [envelope, unitProfile, hij]
  exact congrArg₂ Profile.mk
    (funext fun i => funext fun j => hval i j)
    (funext fun i => funext fun j => hval i j)

theorem unit_positive (n : ℕ) : PositiveUpper (unitProfile n) := by
  intro i j hij
  simp [unitProfile, hij]

theorem two_le_height {n : ℕ} (P : Profile n) : 2 ≤ height P := le_max_left _ _

theorem zero_le_height {n : ℕ} (P : Profile n) (i j : Fin n) : P.zero i j ≤ height P := by
  apply le_trans (le_max_left (P.zero i j) (P.one i j))
  apply le_trans _ (le_max_right _ _)
  exact Finset.le_sup (f := fun ij : Fin n × Fin n =>
    max (P.zero ij.1 ij.2) (P.one ij.1 ij.2)) (Finset.mem_univ (i,j))

theorem one_le_height {n : ℕ} (P : Profile n) (i j : Fin n) : P.one i j ≤ height P := by
  apply le_trans (le_max_right (P.zero i j) (P.one i j))
  apply le_trans _ (le_max_right _ _)
  exact Finset.le_sup (f := fun ij : Fin n × Fin n =>
    max (P.zero ij.1 ij.2) (P.one ij.1 ij.2)) (Finset.mem_univ (i,j))

theorem orbit_eq_fold_take {n p : ℕ} (recipes : Fin (p+1) → Recipe n)
    (P : Profile n) (d : ℕ) (hd : d ≤ p+1) :
    orbit recipes P d = ((List.ofFn recipes).take d).foldl
      (fun Q C => step C Q) (normalize P) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hlt : d < p+1 := by omega
    have hlist : d < (List.ofFn recipes).length := by simpa using hlt
    rw [orbit, ih (by omega), List.take_succ_eq_append_getElem hlist,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    congr 1
    simp only [periodicRecipe, Nat.mod_eq_of_lt hlt, List.getElem_ofFn]

theorem run_ofFn {n p : ℕ} (recipes : Fin (p+1) → Recipe n) (P : Profile n) :
    run (List.ofFn recipes) P = orbit recipes P (p+1) := by
  rw [orbit_eq_fold_take recipes P (p+1) le_rfl]
  have ht : (List.ofFn recipes).take (p+1) = List.ofFn recipes := by
    simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn recipes))
  rw [ht]
  rfl

theorem orbit_exists_of_word (n : ℕ) (word : List (Recipe (n+1)))
    (hw : Crosses215 word) :
    ∃ (n p radius : ℕ)
      (recipes : Fin (p+1) → Recipe (n+1)) (initial : Profile (n+1)),
      1 < radius ∧ radius^43 < (14055^(p+1))^20 ∧
      PositiveUpper initial ∧
      (∀ d, (recipes d).Valid ∧
        ∀ i, 3 ≤ i.val → 0 < (recipes d).tol i → (recipes d).tol i < 6) ∧
      ReturnsWithin recipes initial radius := by
  obtain ⟨hnil, hvalid, hgap⟩ := hw
  have hlen : 0 < word.length := List.length_pos_iff.mpr hnil
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen)
  let recipes : Fin (p+1) → Recipe (n+1) :=
    fun i => word[i.val]'(by omega)
  have hword : List.ofFn recipes = word := by
    apply List.ext_getElem
    · simp [hp]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  let radius := height (run word (unitProfile (n+1)))
  refine ⟨n,p,radius,recipes,unitProfile (n+1), ?_, ?_, unit_positive _, ?_, ?_⟩
  · exact lt_of_lt_of_le (by decide : 1 < 2) (two_le_height _)
  · simpa [radius, hp, pow_mul, Nat.mul_comm] using hgap
  · intro d
    exact hvalid _ (List.getElem_mem (by omega))
  · intro i j hij
    rw [← run_ofFn recipes, hword, normalize_unit]
    change (run word (unitProfile (n+1))).zero i j ≤
        (if i ≤ j then 1 else 0) * radius ∧
      (run word (unitProfile (n+1))).one i j ≤
        (if i ≤ j then 1 else 0) * radius
    simp only [if_pos hij, one_mul]
    exact ⟨zero_le_height _ i j, one_le_height _ i j⟩

end SensitivityProfileWord


set_option autoImplicit false
namespace SensitivityProfileWord
open SensitivityProfileCycle SensitivityProfileSearch

theorem word_exists_of_orbit_data
    (n p radius : ℕ)
    (recipes : Fin (p+1) → Recipe (n+1)) (initial : Profile (n+1))
    (hradius : 1 < radius)
    (hgap : radius^43 < (14055^(p+1))^20)
    (hpositive : PositiveUpper initial)
    (hvalid : ∀ d, (recipes d).Valid ∧
      ∀ i, 3 ≤ i.val → 0 < (recipes d).tol i → (recipes d).tol i < 6)
    (hreturn : ReturnsWithin recipes initial radius) :
    ∃ word : List (Recipe (n+1)), Crosses215 word := by
  apply word_crossing_of_return (List.ofFn recipes) initial radius
  · intro hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_ofFn, List.length_nil] at hlen
    omega
  · intro C hC
    obtain ⟨d, rfl⟩ := List.mem_ofFn.mp hC
    exact hvalid d
  · exact hradius
  · simpa only [List.length_ofFn, ← pow_mul, Nat.mul_comm] using hgap
  · exact hpositive
  · rw [run_ofFn]
    intro i j
    by_cases hij : i ≤ j
    · have h := hreturn i j hij
      exact ⟨h.1.trans (Nat.mul_le_mul_right radius (envelope_le initial.zero i j)),
        h.2.trans (Nat.mul_le_mul_right radius (envelope_le initial.one i j))⟩
    · simp only [orbit, step, envelope, dif_neg hij, scale, Nat.zero_le, and_self]

theorem canonical_word_iff_orbit :
    (∃ (n p radius : ℕ)
      (recipes : Fin (p+1) → Recipe (n+1)) (initial : Profile (n+1)),
      1 < radius ∧ radius^43 < (14055^(p+1))^20 ∧
      PositiveUpper initial ∧
      (∀ d, (recipes d).Valid ∧
        ∀ i, 3 ≤ i.val → 0 < (recipes d).tol i → (recipes d).tol i < 6) ∧
      ReturnsWithin recipes initial radius) ↔
    ∃ (n : ℕ) (word : List (Recipe (n+1))), Crosses215 word := by
  constructor
  · rintro ⟨n,p,radius,recipes,initial,hradius,hgap,hpositive,hvalid,hreturn⟩
    obtain ⟨word,hword⟩ := word_exists_of_orbit_data n p radius recipes initial
      hradius hgap hpositive hvalid hreturn
    exact ⟨n,word,hword⟩
  · rintro ⟨n,word,hword⟩
    exact orbit_exists_of_word n word hword

end SensitivityProfileWord


/- A finite lower-growth calibration for the accepted static q5 recipe.
The recipe is from accepted Prove2Me source a9d25c46-43bd-4fb1-826b-0ed075b8cf0a
(yousofy with Codex, retaining OpenAI/math, Robin Kothari/Codex and community
attributions). The integer profile and lower-growth check are new.
This does not obstruct other recipes in the open search theorem. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace SensitivityProfileObstruction
open SensitivityProfileCycle SensitivityProfileSearch

def sourceRecipe : Recipe 16 where
  target := ![7, 8, 8, 8, 8, 9, 10, 10, 10, 11, 11, 12, 13, 14, 15, 15]
  gate := ![15, 15, 15, 8, 8, 8, 8, 8, 8, 8, 7, 6, 5, 4, 3, 1]
  aux := ![0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  tol := ![0, 0, 0, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0]

def lowerProfile : Profile 16 where
  zero := ![![3637635713710529202487, 31176003979183998634, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1221119003829612377618, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 610559501914806188809, 2345799580462435730, 2128595915604802792, 1866682618393454369, 103233273042083597, 83702653817905619, 64172034593727641, 63896371045659784, 2816984390479370, 171907465668094, 29218552803035, 23611277666475, 1226, 1000], ![0, 0, 0, 135401868346512751921, 2128595915604802792, 1866682618393454369, 103233273042083597, 83702653817905619, 64172034593727641, 63896371045659784, 2816984390479370, 171907465668094, 29218552803035, 23611277666475, 1226, 1000], ![0, 0, 0, 0, 105616649400310604274, 1866682618393454369, 103233273042083597, 83702653817905619, 64172034593727641, 63896371045659784, 2816984390479370, 171907465668094, 29218552803035, 23611277666475, 1226, 1000], ![0, 0, 0, 0, 0, 76475773189932851062, 105464839326753078, 85041593588707308, 64172034593727641, 63896371045659784, 2816984390479370, 171907465668094, 29218552803035, 23611277666475, 88652, 88426], ![0, 0, 0, 0, 0, 0, 22824744560275689374, 202142071189259322, 98071663462985167, 63896371045659784, 2816984390479370, 171907465668094, 29218552803035, 23611277666475, 88652, 88426], ![0, 0, 0, 0, 0, 0, 0, 11443063253204410081, 98071663462985167, 63896371045659784, 2816984390479370, 171907465668094, 29218552803035, 23611277666475, 88652, 88426], ![0, 0, 0, 0, 0, 0, 0, 0, 3841325272853906282, 3838715860768460305, 246718611405881807, 245658783270073132, 14616857083803926, 2111477750942178, 2087869872798558, 88426], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3838715860768460305, 286184667252445173, 245658783270073132, 14616857083803926, 2111477750942178, 2087869872798558, 7819300], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3737791744302306045, 245658783270073132, 14616857083803926, 2111477750942178, 2087869872798558, 7819300], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3735516052543951927, 14616857083803926, 2971904244359543, 2087869872798558, 691435729], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3580435720919952673, 79117990247945530, 78172636599998592, 61141453167], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3573689925105137168, 83600010299841576, 5406543426066], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3533714716022779301, 478083367399509], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42275385245607157]]
  one := ![![3695510648130340191, 243903571080479319, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 3696001910168064338, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 7392003820336128677, 7392003820336128677, 7392003820336128677, 6912551175179587294, 184623363869003435, 184623363869003435, 184623363869003435, 179859983821006202, 179859983821006202, 118837319172796018, 118742402199503763, 115339751606419130, 300608928231, 300608928231], ![0, 0, 0, 312432830746395826849, 7392003820336128677, 6912551175179587294, 184623363869003435, 184623363869003435, 184623363869003435, 179859983821006202, 179859983821006202, 118837319172796018, 118742402199503763, 115339751606419130, 300608928231, 300608928231], ![0, 0, 0, 0, 312476271479367353437, 6912551175179587294, 184623363869003435, 184623363869003435, 184623363869003435, 179859983821006202, 179859983821006202, 118837319172796018, 118742402199503763, 115339751606419130, 300608928231, 300608928231], ![0, 0, 0, 0, 0, 313032356834755201542, 1176720631441866335, 1176720631441866335, 1176720631441866335, 182330048142824892, 182330048142824892, 121265650129264541, 119549344339338272, 115352741941200558, 13290943709659, 13290943709659], ![0, 0, 0, 0, 0, 0, 326738762920645449247, 21567613795671171311, 21567613795671171311, 369380743484292920, 369380743484292920, 158775501457493706, 154652655512487676, 150456053114349962, 13290943709659, 13290943709659], ![0, 0, 0, 0, 0, 0, 0, 326782203653616975835, 21567613795671171311, 369380743484292920, 369380743484292920, 158775501457493706, 154652655512487676, 150456053114349962, 13290943709659, 13290943709659], ![0, 0, 0, 0, 0, 0, 0, 0, 326825644386588502422, 305627411334401624031, 8162827202457112500, 7952221960430313287, 5254202292073174159, 5250005689675036445, 5099562927504396142, 13290943709659], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 349491407707976372005, 52026823576031860475, 8061431909894057852, 5361567067433319692, 5285683347755861649, 5100137274412071943, 587637851385460], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 953577601956756255618, 16331579697122190320, 7020005243218269547, 6837720193665635796, 6652174120321846090, 587637851385460], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1955708131522641699058, 11848548757863270240, 11584682281938108247, 8229604797561384399, 25981469181149623], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6273771889283911400180, 153313949024300637108, 149488122309350938736, 1148729169197506544], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8687176192961769755246, 219942044388659003522, 50789225773367337577], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13005524871659593412741, 2245564510614918791330], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99284048822366933683811]]

theorem lowerProfile_grows : ∀ i j : Fin 16,
    88 * lowerProfile.zero i j ≤ (step sourceRecipe lowerProfile).zero i j ∧
    88 * lowerProfile.one i j ≤ (step sourceRecipe lowerProfile).one i j := by
  decide

theorem lowerProfile_nonzero : 0 < lowerProfile.zero 0 0 := by decide

theorem rate_above_target : 14055 ^ 20 < (88 : ℕ) ^ 43 := by decide

end SensitivityProfileObstruction


set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace SensitivityProfileObstruction
open SensitivityProfileCycle SensitivityProfileSearch SensitivityProfileWord

def maximumEntry : ℕ := lowerProfile.one 15 15

theorem maximumEntry_pos : 0 < maximumEntry := by decide

theorem lowerProfile_bounded :
    ProfileLE lowerProfile (scale (unitProfile 16) maximumEntry) := by
  unfold ProfileLE
  decide

theorem fold_replicate_succ {n : ℕ} (C : Recipe n) (P : Profile n) (m : ℕ) :
    (List.replicate (m+1) C).foldl (fun Q C => step C Q) P =
      step C ((List.replicate m C).foldl (fun Q C => step C Q) P) := by
  rw [List.replicate_succ', List.foldl_append]
  rfl

theorem lowerProfile_iterates (m : ℕ) :
    ProfileLE (scale lowerProfile (88^m))
      ((List.replicate m sourceRecipe).foldl
        (fun Q C => step C Q) lowerProfile) := by
  induction m with
  | zero =>
      simp only [List.replicate_zero, List.foldl_nil, pow_zero, scale, Nat.mul_one]
      intro i j
      exact ⟨le_rfl, le_rfl⟩
  | succ m ih =>
      rw [fold_replicate_succ]
      have hstep := step_mono sourceRecipe _ _ ih
      rw [step_mul] at hstep
      have hbase : ProfileLE (scale lowerProfile 88) (step sourceRecipe lowerProfile) := by
        intro i j
        simpa only [scale, Nat.mul_comm] using lowerProfile_grows i j
      have h := profileLE_trans (scale_mono hbase (88^m)) hstep
      simpa only [scale, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem source_height_lower (m : ℕ) :
    88^m ≤ height (run (List.replicate m sourceRecipe) (unitProfile 16)) := by
  have hupper := fold_mono (List.replicate m sourceRecipe) _ _ lowerProfile_bounded
  rw [fold_mul] at hupper
  have hrun : (List.replicate m sourceRecipe).foldl
      (fun Q C => step C Q) (unitProfile 16) =
        run (List.replicate m sourceRecipe) (unitProfile 16) := by
    simp only [run, normalize_unit]
  rw [hrun] at hupper
  have h := profileLE_trans (lowerProfile_iterates m) hupper
  have hcoord := (h 15 15).2
  have hmax := (le_height (run (List.replicate m sourceRecipe) (unitProfile 16)) 15 15).2
  have hcoord' : (88^m) * maximumEntry ≤
      (run (List.replicate m sourceRecipe) (unitProfile 16)).one 15 15 * maximumEntry := by
    simpa only [scale, maximumEntry, Nat.mul_comm] using hcoord
  have hmul : (88^m) * maximumEntry ≤
      height (run (List.replicate m sourceRecipe) (unitProfile 16)) * maximumEntry := by
    exact hcoord'.trans (Nat.mul_le_mul_right maximumEntry hmax)
  exact Nat.le_of_mul_le_mul_right hmul maximumEntry_pos

/-- Repeating the accepted static recipe cannot cross the 2.15 threshold,
regardless of the length of the word. Other recipes remain unrestricted. -/
theorem source_replicate_not_crosses (m : ℕ) :
    ¬ Crosses215 (List.replicate m sourceRecipe) := by
  intro hcross
  have hm : m ≠ 0 := by
    intro h
    exact hcross.1 (by simp [h])
  have hgap := hcross.2.2
  simp only [List.length_replicate] at hgap
  have hrate := Nat.pow_lt_pow_left rate_above_target hm
  have hrate' : 14055^(20*m) < (88^m)^43 := by
    simpa only [← pow_mul, Nat.mul_comm] using hrate
  have hheight : (88^m)^43 ≤
      height (run (List.replicate m sourceRecipe) (unitProfile 16))^43 := by
    exact Nat.pow_le_pow_left (source_height_lower m) 43
  exact (not_lt_of_ge hheight) (hgap.trans hrate')

end SensitivityProfileObstruction

theorem solution :
    (∃ (n p radius : ℕ)
      (recipes : Fin (p+1) → SensitivityProfileCycle.Recipe (n+1))
      (initial : SensitivityProfileSearch.Profile (n+1)),
      1 < radius ∧ radius^43 < (14055^(p+1))^20 ∧
      SensitivityProfileSearch.PositiveUpper initial ∧
      (∀ d, (recipes d).Valid ∧
        ∀ i, 3 ≤ i.val → 0 < (recipes d).tol i → (recipes d).tol i < 6) ∧
      SensitivityProfileSearch.ReturnsWithin recipes initial radius) ↔
    ∃ (n : ℕ) (word : List (SensitivityProfileCycle.Recipe (n+1))),
      SensitivityProfileWord.Crosses215 word := by
  exact SensitivityProfileWord.canonical_word_iff_orbit
