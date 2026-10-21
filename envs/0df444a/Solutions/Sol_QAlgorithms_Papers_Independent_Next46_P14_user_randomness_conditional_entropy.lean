-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P14.user_randomness_conditional_entropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:31:30.573147+00:00
-- url     : https://prove2.me/submissions/2f8b1059-79f0-40b7-9515-816ff5eef639

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Next46.P14

theorem g62g_tsum_map {O B : Type*} (P : PMF O) (g : O → B) (ψ : B → ℝ≥0∞) :
    ∑' y, (P.map g) y * ψ y = ∑' x, P x * ψ (g x) := by
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun x => ?_)
  simp only [ite_mul, zero_mul]
  rw [tsum_ite_eq]

theorem g62g_term (J : ℝ≥0∞) (hJ : J ≠ ⊤) (r l : ℝ) :
    ENNReal.ofReal (-J.toReal * Real.log r / l) = J * ENNReal.ofReal (-Real.log r / l) := by
  rw [show -J.toReal * Real.log r / l = J.toReal * (-Real.log r / l) by ring,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hJ]

theorem g62g_le_map {O B : Type*} (P : PMF O) (g : O → B) (x : O) : P x ≤ (P.map g) (g x) := by
  rw [PMF.map_apply]
  exact le_of_eq_of_le (by simp) (ENNReal.le_tsum x)

theorem g62g_joint_le {O A C : Type*} (P : PMF O) (X : O → A) (Y : O → C) (a : A) (c : C) :
    (P.map (fun x => (X x, Y x))) (a, c) ≤ (P.map Y) c := by
  have : P.map Y = (P.map (fun x => (X x, Y x))).map Prod.snd := by
    rw [PMF.map_comp]; rfl
  rw [this]
  exact g62g_le_map _ Prod.snd (a, c)

theorem g62g_ce_cond {O A C D : Type*} (p : ℕ) (P : PMF O) (X : O → A) (Y : O → C)
    (f : C → D)
    (hci : ∀ a c, (P.map (fun x => (X x, Y x))) (a, c) * (P.map (fun x => f (Y x))) (f c) =
      (P.map (fun x => (X x, f (Y x)))) (a, f c) * (P.map Y) c) :
    spirConditionalEntropy p P X Y = spirConditionalEntropy p P X (fun x => f (Y x)) := by
  set J1 := P.map (fun x => (X x, Y x)) with hJ1
  set J2 := P.map (fun x => (X x, f (Y x))) with hJ2
  set M1 := P.map Y with hM1
  set M2 := P.map (fun x => f (Y x)) with hM2
  let φ : A × D → ℝ≥0∞ := fun ad =>
    ENNReal.ofReal (-Real.log ((J2 ad).toReal / (M2 ad.2).toReal) / Real.log p)
  have hL : spirConditionalEntropy p P X Y = ∑' ac : A × C, J1 ac * φ (ac.1, f ac.2) := by
    unfold spirConditionalEntropy
    dsimp only
    rw [← hJ1, ← hM1]
    refine tsum_congr (fun ac => ?_)
    obtain ⟨a, c⟩ := ac
    rw [g62g_term _ (PMF.apply_ne_top _ _)]
    by_cases h0 : J1 (a, c) = 0
    · simp [h0]
    congr 1
    simp only [φ]
    congr 2
    have hM1c : M1 c ≠ 0 := by
      intro h; apply h0; exact le_antisymm (h ▸ g62g_joint_le P X Y a c) (zero_le)
    have hM2c : M2 (f c) ≠ 0 := by
      intro h; apply hM1c
      have : M1 c ≤ M2 (f c) := by
        have e : M2 = M1.map f := by rw [hM2, hM1, PMF.map_comp]; rfl
        rw [e]; exact g62g_le_map M1 f c
      exact le_antisymm (h ▸ this) (zero_le)
    have h := congrArg ENNReal.toReal (hci a c)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at h
    have t1 : (M1 c).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hM1c, PMF.apply_ne_top _ _⟩
    have t2 : (M2 (f c)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hM2c, PMF.apply_ne_top _ _⟩
    rw [div_eq_div_iff t1 t2 |>.mpr h]
  have hR : spirConditionalEntropy p P X (fun x => f (Y x)) = ∑' ad : A × D, J2 ad * φ ad := by
    unfold spirConditionalEntropy
    dsimp only
    rw [← hJ2, ← hM2]
    refine tsum_congr (fun ad => ?_)
    rw [g62g_term _ (PMF.apply_ne_top _ _)]
  rw [hL, hR, g62g_tsum_map P (fun x => (X x, Y x)) (fun ac => φ (ac.1, f ac.2)),
    g62g_tsum_map P (fun x => (X x, f (Y x))) φ]

theorem g62g_dl_map {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L) {Z : Type*}
    (V : Messages m L × ℕ × ℕ → Z) (z : Z) :
    (dataLaw b).map V z = ∑' h, b.userSeed h * ∑' w, (PMF.uniformOfFintype (Messages m L)) w *
      ∑' s, (if z = V (w, h, s) then b.sharedSeed s else 0) := by
  unfold dataLaw
  simp only [PMF.map_bind, PMF.map_comp, PMF.bind_apply, PMF.map_apply]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun h => tsum_congr (fun w => tsum_congr (fun s => ?_)))
  simp only [Function.comp]
  split_ifs <;> ring

theorem g62g_zero {W : Type*} (μh : ℝ≥0∞) (c : W → ℕ → Prop) (ν : ℕ → ℝ≥0∞)
    (u : W → ℝ≥0∞) (hc : ∀ w s, ¬ c w s) :
    μh * ∑' w, u w * ∑' s, (if c w s then ν s else 0) = 0 := by
  simp [hc]

section
variable {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L) (k : Fin m.K) (n : Fin m.N)

def g62g_F (a : List (ZMod m.p)) (x0 : Message m L k) (q : ℕ) : ℝ≥0∞ :=
  ∑' w, (PMF.uniformOfFintype (Messages m L)) w *
    ∑' s, (if a = b.answer n q w s ∧ x0 = w k then b.sharedSeed s else 0)

def g62g_G (x0 : Message m L k) : ℝ≥0∞ :=
  ∑' w, (PMF.uniformOfFintype (Messages m L)) w *
    ∑' s, (if x0 = w k then b.sharedSeed s else 0)

def g62g_pi (q : ℕ) : ℝ≥0∞ := ∑' h, if q = b.query k h n then b.userSeed h else 0

theorem g62g_J1 (a : List (ZMod m.p)) (x0 : Message m L k) (h0 q : ℕ) :
    (dataLaw b).map (fun x => (observedAnswer b k n x, (x.1 k, x.2.1, b.query k x.2.1 n)))
      (a, (x0, h0, q)) =
    if q = b.query k h0 n then b.userSeed h0 * g62g_F b k n a x0 q else 0 := by
  rw [g62g_dl_map, tsum_eq_single h0]
  · split_ifs with hq
    · subst hq
      unfold g62g_F
      congr 1
      refine tsum_congr (fun w => ?_)
      congr 1
      refine tsum_congr (fun s => ?_)
      simp [observedAnswer, Prod.ext_iff]
    · first | rw [zero_mul] | skip

      exact g62g_zero _ _ _ _ (fun w s e => by simp [Prod.ext_iff] at e; tauto)
  · intro h hh
    first | rw [zero_mul] | skip

    exact g62g_zero _ _ _ _ (fun w s e => by simp [Prod.ext_iff] at e; tauto)

theorem g62g_M1 (x0 : Message m L k) (h0 q : ℕ) :
    (dataLaw b).map (fun x => (x.1 k, x.2.1, b.query k x.2.1 n)) (x0, h0, q) =
    if q = b.query k h0 n then b.userSeed h0 * g62g_G b k x0 else 0 := by
  rw [g62g_dl_map, tsum_eq_single h0]
  · split_ifs with hq
    · subst hq
      unfold g62g_G
      congr 1
      refine tsum_congr (fun w => ?_)
      congr 1
      refine tsum_congr (fun s => ?_)
      simp [Prod.ext_iff]
    · first | rw [zero_mul] | skip

      exact g62g_zero _ _ _ _ (fun w s e => by simp [Prod.ext_iff] at e; tauto)
  · intro h hh
    first | rw [zero_mul] | skip

    exact g62g_zero _ _ _ _ (fun w s e => by simp [Prod.ext_iff] at e; tauto)

theorem g62g_J2 (a : List (ZMod m.p)) (x0 : Message m L k) (q : ℕ) :
    (dataLaw b).map (fun x => (observedAnswer b k n x, (x.1 k, b.query k x.2.1 n)))
      (a, (x0, q)) = g62g_pi b k n q * g62g_F b k n a x0 q := by
  rw [g62g_dl_map, g62g_pi, ← ENNReal.tsum_mul_right]
  refine tsum_congr (fun h => ?_)
  split_ifs with hq
  · subst hq
    unfold g62g_F
    congr 1
    refine tsum_congr (fun w => ?_)
    congr 1
    refine tsum_congr (fun s => ?_)
    simp [observedAnswer, Prod.ext_iff]
  · first | rw [zero_mul] | skip

    exact g62g_zero _ _ _ _ (fun w s e => by simp [Prod.ext_iff] at e; tauto)

theorem g62g_M2 (x0 : Message m L k) (q : ℕ) :
    (dataLaw b).map (fun x => (x.1 k, b.query k x.2.1 n)) (x0, q) =
      g62g_pi b k n q * g62g_G b k x0 := by
  rw [g62g_dl_map, g62g_pi, ← ENNReal.tsum_mul_right]
  refine tsum_congr (fun h => ?_)
  split_ifs with hq
  · subst hq
    unfold g62g_G
    congr 1
    refine tsum_congr (fun w => ?_)
    congr 1
    refine tsum_congr (fun s => ?_)
    simp [Prod.ext_iff]
  · first | rw [zero_mul] | skip

    exact g62g_zero _ _ _ _ (fun w s e => by simp [Prod.ext_iff] at e; tauto)

end

theorem solution {m : SpirParameters} {L : ℕ}
    (b : SpirProtocol m L) (hprivate : Private b) (k : Fin m.K) (n : Fin m.N) :
    spirConditionalEntropy m.p (dataLaw b) (observedAnswer b k n)
      (fun x => (x.1 k, x.2.1, b.query k x.2.1 n)) =
    spirConditionalEntropy m.p (dataLaw b) (observedAnswer b k n)
      (fun x => (x.1 k, b.query k x.2.1 n)) := by
  refine g62g_ce_cond m.p (dataLaw b) (observedAnswer b k n)
    (fun x => (x.1 k, x.2.1, b.query k x.2.1 n)) (fun c => (c.1, c.2.2)) ?_
  rintro a ⟨x0, h0, q⟩
  simp only
  rw [g62g_J1, g62g_M1, g62g_J2, g62g_M2]
  split_ifs <;> ring
