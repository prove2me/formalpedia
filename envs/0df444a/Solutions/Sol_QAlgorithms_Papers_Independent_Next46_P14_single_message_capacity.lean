-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P14.single_message_capacity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:00:43.198119+00:00
-- url     : https://prove2.me/submissions/493f0b1e-f63a-4fba-9ec7-a46bcfcbf926

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Next46.P14

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

theorem g62g_indep_fun {O X' Y' A B : Type*} (P : PMF O) (X : O → X') (Y : O → Y')
    (hI : Independent P X Y) (f : X' → A) (g : Y' → B) (a : A) (c : B) :
    (P.map (fun x => (f (X x), g (Y x)))) (a, c) =
      (P.map (fun x => f (X x))) a * (P.map (fun x => g (Y x))) c := by
  have e1 : P.map (fun x => (f (X x), g (Y x))) =
      (P.map (fun x => (X x, Y x))).map (Prod.map f g) := by
    rw [PMF.map_comp]; rfl
  have e2 : P.map (fun x => f (X x)) = (P.map X).map f := by rw [PMF.map_comp]; rfl
  have e3 : P.map (fun x => g (Y x)) = (P.map Y).map g := by rw [PMF.map_comp]; rfl
  rw [e1, e2, e3, PMF.map_apply, PMF.map_apply, PMF.map_apply, ENNReal.tsum_prod',
    ← ENNReal.tsum_mul_right]
  refine tsum_congr (fun x => ?_)
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun y => ?_)
  rw [hI x y]
  simp only [Prod.map, Prod.mk.injEq]
  split_ifs <;> simp_all

section
variable {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L)

def g62g_F (j : Fin m.K) (n : Fin m.N) (x0 : Message m L j) (q : ℕ) (a : List (ZMod m.p)) : ℝ≥0∞ :=
  ∑' w, (PMF.uniformOfFintype (Messages m L)) w *
    ∑' s, (if x0 = w j ∧ a = b.answer n q w s then b.sharedSeed s else 0)

def g62g_G (n : Fin m.N) (q : ℕ) (a : List (ZMod m.p)) : ℝ≥0∞ :=
  ∑' w, (PMF.uniformOfFintype (Messages m L)) w *
    ∑' s, (if a = b.answer n q w s then b.sharedSeed s else 0)

def g62g_pi (k : Fin m.K) (n : Fin m.N) (q : ℕ) : ℝ≥0∞ :=
  ∑' h, if q = b.query k h n then b.userSeed h else 0

theorem g62g_one (w0 : Messages m L) (c : ℕ → Prop) (hc : ∀ s, c s) :
    ∑' w, (PMF.uniformOfFintype (Messages m L)) w *
      ∑' s, (if c s then b.sharedSeed s else 0) = 1 := by
  simp only [hc, if_true, PMF.tsum_coe, mul_one]

theorem g62g_L1 (k : Fin m.K) (n : Fin m.N) (q : ℕ) :
    (dataLaw b).map (fun x => b.query k x.2.1 n) q = g62g_pi b k n q := by
  rw [g62g_dl_map, g62g_pi]
  refine tsum_congr (fun h => ?_)
  split_ifs with hq
  · simp only [hq, if_true, PMF.tsum_coe, mul_one]
  · simp [hq]

theorem g62g_L2 (j k : Fin m.K) (n : Fin m.N) (x0 : Message m L j) (q : ℕ) (a : List (ZMod m.p)) :
    (dataLaw b).map (fun x => (x.1 j, (b.query k x.2.1 n, observedAnswer b k n x)))
      (x0, (q, a)) = g62g_pi b k n q * g62g_F b j n x0 q a := by
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
  · rw [zero_mul]
    exact g62g_zero _ _ _ _ (fun w s e => by simp [Prod.ext_iff] at e; tauto)

theorem g62g_L3 (k : Fin m.K) (n : Fin m.N) (q : ℕ) (a : List (ZMod m.p)) :
    (dataLaw b).map (fun x => (b.query k x.2.1 n, observedAnswer b k n x))
      (q, a) = g62g_pi b k n q * g62g_G b n q a := by
  rw [g62g_dl_map, g62g_pi, ← ENNReal.tsum_mul_right]
  refine tsum_congr (fun h => ?_)
  split_ifs with hq
  · subst hq
    unfold g62g_G
    congr 1
    refine tsum_congr (fun w => ?_)
    congr 1
    refine tsum_congr (fun s => ?_)
    simp [observedAnswer, Prod.ext_iff]
  · rw [zero_mul]
    exact g62g_zero _ _ _ _ (fun w s e => by simp [Prod.ext_iff] at e; tauto)

theorem g62g_L6 (n : Fin m.N) (q : ℕ) : ∑' a, g62g_G b n q a = 1 := by
  unfold g62g_G
  rw [ENNReal.tsum_comm]
  conv_rhs => rw [← PMF.tsum_coe (PMF.uniformOfFintype (Messages m L))]
  refine tsum_congr (fun w => ?_)
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
  simp only [tsum_ite_eq, PMF.tsum_coe, mul_one]

def g62g_cw (k : Fin m.K) (x0 : Message m L k) : ℝ≥0∞ :=
  ∑' w, (PMF.uniformOfFintype (Messages m L)) w * (if x0 = w k then 1 else 0)

theorem g62g_c_eq (k : Fin m.K) (x0 : Message m L k) :
    (dataLaw b).map (fun x => x.1 k) x0 = g62g_cw (m := m) (L := L) k x0 := by
  rw [g62g_dl_map]
  rw [show g62g_cw (m := m) (L := L) k x0 = ∑' h, b.userSeed h * g62g_cw (m := m) (L := L) k x0 by
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]]
  refine tsum_congr (fun h => ?_)
  congr 1
  unfold g62g_cw
  refine tsum_congr (fun w => ?_)
  congr 1
  split_ifs with hx
  · simp [PMF.tsum_coe]
  · simp

theorem g62g_cw_transl (k : Fin m.K) (x0 x1 : Message m L k) :
    g62g_cw (m := m) (L := L) k x1 = g62g_cw (m := m) (L := L) k x0 := by
  unfold g62g_cw
  let δ : Messages m L := Pi.single k (x1 - x0)
  rw [← (Equiv.addRight δ).tsum_eq]
  refine tsum_congr (fun w => ?_)
  simp only [Equiv.coe_addRight, PMF.uniformOfFintype_apply, Pi.add_apply, δ, Pi.single_eq_same]
  congr 1
  have : (x1 = w k + (x1 - x0)) ↔ (x0 = w k) := by
    rw [eq_comm, ← eq_sub_iff_add_eq, sub_sub_cancel, eq_comm]
  simp only [this]

theorem g62g_cw_sum (k : Fin m.K) : ∑' x0, g62g_cw (m := m) (L := L) k x0 = 1 := by
  unfold g62g_cw
  rw [ENNReal.tsum_comm]
  conv_rhs => rw [← PMF.tsum_coe (PMF.uniformOfFintype (Messages m L))]
  refine tsum_congr (fun w => ?_)
  rw [ENNReal.tsum_mul_left]
  simp only [tsum_ite_eq, mul_one]

theorem g62g_cw_le (hL : 0 < L) (k : Fin m.K) (x0 : Message m L k) :
    g62g_cw (m := m) (L := L) k x0 ≤ 2⁻¹ := by
  haveI : Fact (1 < m.p) := ⟨m.prime.one_lt⟩
  have hpos : 0 < m.ell k * L := Nat.mul_pos (m.ell_pos k) hL
  let i0 : Fin (m.ell k * L) := ⟨0, hpos⟩
  let x1 : Message m L k := x0 + Pi.single i0 1
  have hne : x0 ≠ x1 := by
    intro h
    have := congrFun h i0
    simp [x1] at this
  have h2 := ENNReal.sum_le_tsum (f := g62g_cw (m := m) (L := L) k) ({x0, x1} : Finset _)
  rw [Finset.sum_pair hne, g62g_cw_sum, g62g_cw_transl k x0 x1] at h2
  rw [ENNReal.le_inv_iff_mul_le]
  calc _ = g62g_cw (m := m) (L := L) k x0 + g62g_cw (m := m) (L := L) k x0 := by ring
    _ ≤ 1 := h2

theorem g62g_err (hK : 2 ≤ m.K) (hN : m.N = 1) (hpriv : Private b) (k : Fin m.K) :
    (2 : ℝ≥0∞)⁻¹ ≤ (dataLaw b).map (fun x => decide (b.decode k x.2.1 (b.query k x.2.1)
      (fun n => observedAnswer b k n x) ≠ x.1 k)) true := by
  let n0 : Fin m.N := ⟨0, by omega⟩
  have hn0 : ∀ n : Fin m.N, n = n0 := fun n => Fin.ext (by have := n.2; simp [n0]; omega)
  obtain ⟨k2, hk2⟩ : ∃ k2 : Fin m.K, k ≠ k2 := by
    by_cases h : k.val = 0
    · exact ⟨⟨1, by omega⟩, fun e => by rw [e] at h; simp at h⟩
    · exact ⟨⟨0, by omega⟩, fun e => h (by rw [e])⟩
  have hpi : g62g_pi b k n0 = g62g_pi b k2 n0 := by
    funext q
    rw [← g62g_L1, ← g62g_L1]
    have := congrArg (PMF.map Prod.fst) (hpriv.1 k k2 n0)
    simp only [PMF.map_comp] at this
    exact DFunLike.congr_fun this q
  have hpi_top : ∀ q, g62g_pi b k n0 q ≠ ⊤ := fun q => by
    rw [← g62g_L1]; exact PMF.apply_ne_top _ _
  have hF : ∀ x0 q a, g62g_pi b k n0 q ≠ 0 →
      g62g_F b k n0 x0 q a = g62g_cw (m := m) (L := L) k x0 * g62g_G b n0 q a := by
    intro x0 q a hq
    have h1 : (dataLaw b).map (fun x => (x.1 k, (b.query k2 x.2.1 n0, observedAnswer b k2 n0 x)))
        (x0, (q, a)) = (dataLaw b).map (fun x => x.1 k) x0 *
          (dataLaw b).map (fun x => (b.query k2 x.2.1 n0, observedAnswer b k2 n0 x)) (q, a) :=
      g62g_indep_fun (dataLaw b) (undesired k2) (userView b k2) (hpriv.2 k2)
        (fun v => v ⟨k, hk2⟩) (fun y => (y.1 n0, y.2.1 n0)) x0 (q, a)
    rw [g62g_L2, g62g_L3, g62g_c_eq, ← hpi, mul_left_comm] at h1
    exact (ENNReal.mul_right_inj hq (hpi_top q)).mp h1
  have hS : (dataLaw b).map (fun x => decide (b.decode k x.2.1 (b.query k x.2.1)
      (fun n => observedAnswer b k n x) ≠ x.1 k)) false ≤ 2⁻¹ := by
    rw [g62g_dl_map]
    calc _ ≤ ∑' h, b.userSeed h * 2⁻¹ := by
          refine ENNReal.tsum_le_tsum (fun h => ?_)
          by_cases hμ : b.userSeed h = 0
          · simp [hμ]
          refine mul_le_mul' le_rfl ?_
          set q := b.query k h n0 with hqdef
          have hq : g62g_pi b k n0 q ≠ 0 := by
            intro h0
            apply hμ
            have : b.userSeed h ≤ g62g_pi b k n0 q := by
              unfold g62g_pi
              refine le_trans (le_of_eq ?_) (ENNReal.le_tsum h)
              simp [hqdef]
            exact le_antisymm (h0 ▸ this) zero_le
          let Dh : List (ZMod m.p) → Message m L k := fun a => b.decode k h (b.query k h) (fun _ => a)
          have hfun : ∀ w s, (fun n => observedAnswer b k n ((w, h, s) : Messages m L × ℕ × ℕ)) =
              fun _ => b.answer n0 q w s := by
            intro w s; funext n; obtain rfl := hn0 n; rfl
          refine le_trans (le_of_eq ?_) (show ∑' a, g62g_F b k n0 (Dh a) q a ≤ 2⁻¹ from ?_)
          · unfold g62g_F
            rw [ENNReal.tsum_comm]
            refine tsum_congr (fun w => ?_)
            rw [ENNReal.tsum_mul_left]
            congr 1
            rw [ENNReal.tsum_comm]
            refine tsum_congr (fun s => ?_)
            rw [tsum_eq_single (b.answer n0 q w s)]
            · simp only [hfun, Dh]
              simp
            · intro a ha
              simp [ha]
          calc _ = ∑' a, g62g_cw (m := m) (L := L) k (Dh a) * g62g_G b n0 q a :=
                tsum_congr (fun a => hF _ _ _ hq)
            _ ≤ ∑' a, 2⁻¹ * g62g_G b n0 q a :=
                ENNReal.tsum_le_tsum (fun a => mul_le_mul' (g62g_cw_le b.length_pos k _) le_rfl)
            _ = 2⁻¹ := by rw [ENNReal.tsum_mul_left, g62g_L6, mul_one]
      _ = 2⁻¹ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hsum := PMF.tsum_coe ((dataLaw b).map (fun x => decide (b.decode k x.2.1 (b.query k x.2.1)
      (fun n => observedAnswer b k n x) ≠ x.1 k)))
  rw [tsum_bool] at hsum
  rw [← ENNReal.one_sub_inv_two, tsub_le_iff_left, ← hsum]
  exact add_le_add hS le_rfl

end

theorem g62g_empty (m : SpirParameters) (hK : 2 ≤ m.K) (hN : m.N = 1) :
    IsEmpty (ReliableSequence m) := by
  refine ⟨fun a => ?_⟩
  let k : Fin m.K := ⟨0, by omega⟩
  have hev := (a.reliability k).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨t, ht⟩ := hev.exists
  have h1 := g62g_err (a.block t) hK hN (a.privacy t) k
  have h2 : ((2 : ℝ≥0∞)⁻¹).toReal ≤ errorProbability (a.block t) k :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) h1
  simp at h2
  linarith

section
variable {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L)

theorem g62g_card_le (hK1 : m.K = 1) (k : Fin m.K) (h s : ℕ) :
    (Finset.univ.filter (fun w : Messages m L =>
      b.decode k h (b.query k h) (fun n => b.answer n (b.query k h n) w s) = w k)).card ≤
      m.p ^ (∑ n, b.format n (b.query k h n)) := by
  have hk : ∀ j : Fin m.K, j = k := fun j => Fin.ext (by have := j.2; have := k.2; omega)
  let T := (n : Fin m.N) → List.Vector (ZMod m.p) (b.format n (b.query k h n))
  let φ : Messages m L → T := fun w n => ⟨b.answer n (b.query k h n) w s, b.answer_length _ _ _ _⟩
  have hinj : Set.InjOn φ (Finset.univ.filter (fun w : Messages m L =>
      b.decode k h (b.query k h) (fun n => b.answer n (b.query k h n) w s) = w k) : Set _) := by
    intro w hw w' hw' he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
    have hans : (fun n => b.answer n (b.query k h n) w s) = (fun n => b.answer n (b.query k h n) w' s) := by
      funext n
      have := congrFun he n
      simp only [φ] at this
      exact congrArg Subtype.val this
    have hk' : w k = w' k := by rw [← hw, ← hw', hans]
    funext j
    obtain rfl := hk j
    exact hk'
  have := Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  refine this.trans (le_of_eq ?_)
  rw [Finset.card_univ]
  simp only [T, Fintype.card_pi, card_vector, ZMod.card]
  rw [Finset.prod_pow_eq_pow_sum]

theorem g62g_card_msg (hK1 : m.K = 1) (k : Fin m.K) :
    Fintype.card (Messages m L) = m.p ^ (m.ell k * L) := by
  have hk : ∀ j : Fin m.K, j = k := fun j => Fin.ext (by have := j.2; have := k.2; omega)
  rw [Fintype.card_pi, Finset.prod_eq_single k (fun j _ hj => absurd (hk j) hj) (by simp)]
  simp [Message, ZMod.card]

theorem g62g_conv (hK1 : m.K = 1) (k : Fin m.K) (hD : b.download < m.ell k * L) :
    (2 : ℝ≥0∞)⁻¹ ≤ (dataLaw b).map (fun x => decide (b.decode k x.2.1 (b.query k x.2.1)
      (fun n => observedAnswer b k n x) ≠ x.1 k)) true := by
  have hp2 : 2 ≤ m.p := m.prime.two_le
  have hc : ((m.p : ℝ≥0∞) ^ b.download) * ((Fintype.card (Messages m L) : ℝ≥0∞))⁻¹ ≤ 2⁻¹ := by
    rw [g62g_card_msg hK1 k]
    have h1 : 2 * m.p ^ b.download ≤ m.p ^ (m.ell k * L) :=
      calc 2 * m.p ^ b.download ≤ m.p * m.p ^ b.download := Nat.mul_le_mul_right _ hp2
        _ = m.p ^ (b.download + 1) := by ring
        _ ≤ _ := Nat.pow_le_pow_right m.prime.pos hD
    rw [← div_eq_mul_inv, ENNReal.div_le_iff (by simp [m.prime.ne_zero]) (by simp)]
    calc ((m.p : ℝ≥0∞) ^ b.download) = 2⁻¹ * (2 * (m.p : ℝ≥0∞) ^ b.download) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ 2⁻¹ * ((m.p ^ (m.ell k * L) : ℕ) : ℝ≥0∞) := by
          gcongr
          exact_mod_cast h1
  have hS : (dataLaw b).map (fun x => decide (b.decode k x.2.1 (b.query k x.2.1)
      (fun n => observedAnswer b k n x) ≠ x.1 k)) false ≤ 2⁻¹ := by
    rw [g62g_dl_map]
    calc _ ≤ ∑' h, b.userSeed h * 2⁻¹ := by
          refine ENNReal.tsum_le_tsum (fun h => ?_)
          by_cases hμ : b.userSeed h = 0
          · simp [hμ]
          refine mul_le_mul' le_rfl (le_trans ?_ hc)
          have hDh : ∑ n, b.format n (b.query k h n) ≤ b.download := b.download_bound k h hμ
          have inner : ∀ s, ∑' w, (if b.decode k h (b.query k h)
              (fun n => b.answer n (b.query k h n) w s) = w k
              then (PMF.uniformOfFintype (Messages m L)) w else 0) ≤
              ((m.p : ℝ≥0∞) ^ b.download) * ((Fintype.card (Messages m L) : ℝ≥0∞))⁻¹ := by
            intro s
            rw [tsum_fintype, ← Finset.sum_filter]
            simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul]
            gcongr
            calc ((Finset.univ.filter _).card : ℝ≥0∞) ≤ ((m.p ^ (∑ n, b.format n (b.query k h n)) : ℕ) : ℝ≥0∞) := by
                  exact_mod_cast g62g_card_le b hK1 k h s
              _ ≤ _ := by
                  push_cast
                  exact pow_le_pow_right₀ (by exact_mod_cast m.prime.one_lt.le) hDh
          calc _ = ∑' s, b.sharedSeed s * ∑' w, (if b.decode k h (b.query k h)
                (fun n => b.answer n (b.query k h n) w s) = w k
                then (PMF.uniformOfFintype (Messages m L)) w else 0) := by
                simp_rw [← ENNReal.tsum_mul_left]
                rw [ENNReal.tsum_comm]
                refine tsum_congr fun s => tsum_congr fun w => ?_
                simp only [observedAnswer]
                by_cases hc : (b.decode k h (b.query k h) fun n => b.answer n (b.query k h n) w s) = w k
                · simp [hc, mul_comm]
                · simp [hc]
            _ ≤ ∑' s, b.sharedSeed s * (((m.p : ℝ≥0∞) ^ b.download) *
                  ((Fintype.card (Messages m L) : ℝ≥0∞))⁻¹) :=
                ENNReal.tsum_le_tsum fun s => mul_le_mul' le_rfl (inner s)
            _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ = 2⁻¹ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hsum := PMF.tsum_coe ((dataLaw b).map (fun x => decide (b.decode k x.2.1 (b.query k x.2.1)
      (fun n => observedAnswer b k n x) ≠ x.1 k)))
  rw [tsum_bool] at hsum
  rw [← ENNReal.one_sub_inv_two, tsub_le_iff_left, ← hsum]
  exact add_le_add hS le_rfl

end

theorem g62g_ent_pure (p : ℕ) : spirEntropy p (PMF.pure (0 : ℕ)) = 0 := by
  unfold spirEntropy
  refine ENNReal.tsum_eq_zero.mpr fun a => ?_
  by_cases ha : a = 0 <;> simp [PMF.pure_apply, ha]

theorem g62g_sumf (m : SpirParameters) (E : ℕ) :
    ∑ n : Fin m.N, (if n.val = 0 then E else 0) = E := by
  rw [Finset.sum_eq_single (⟨0, m.N_pos⟩ : Fin m.N)]
  · simp
  · intro n _ hn
    have : n.val ≠ 0 := fun h => hn (Fin.ext h)
    simp [this]
  · simp

def g62g_scheme (m : SpirParameters) (L : ℕ) (hL : 0 < L) : SpirProtocol m L where
  length_pos := hL
  userSeed := PMF.pure 0
  sharedSeed := PMF.pure 0
  query := fun _ _ _ => 0
  format := fun n _ => if n.val = 0 then m.ell ⟨0, m.K_pos⟩ * L else 0
  answer := fun n _ w _ => if n.val = 0 then List.ofFn (w ⟨0, m.K_pos⟩) else []
  answer_length := by
    intro n q w s
    split_ifs <;> simp
  decode := fun _ _ _ ans => fun i => (ans ⟨0, m.N_pos⟩).getD i.val 0
  download := m.ell ⟨0, m.K_pos⟩ * L
  download_bound := by
    intro k h _
    rw [g62g_sumf]
  download_attained := ⟨⟨0, m.K_pos⟩, 0, by simp, g62g_sumf m _⟩

theorem g62g_scheme_ok (m : SpirParameters) (hK1 : m.K = 1) (L : ℕ) (hL : 0 < L) (rho : ℝ) :
    Private (g62g_scheme m L hL) ∧ ZeroError (g62g_scheme m L hL) ∧
      WithinBudget (g62g_scheme m L hL) rho ∧
      ∀ k, spirRate (g62g_scheme m L hL) k = 1 := by
  have hk : ∀ j : Fin m.K, j = ⟨0, m.K_pos⟩ := fun j => Fin.ext (by have := j.2; simp; omega)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k k2 n
    rw [hk k, hk k2]
  · intro k a c
    have hX : ∀ x, undesired k x = a := fun x => by
      funext j; exact absurd (hk j.val ▸ hk k ▸ rfl : j.val = k) j.2
    simp only [PMF.map_apply, hX, Prod.mk.injEq, true_and]
    simp [PMF.tsum_coe]
    refine tsum_congr fun x => ?_
    split_ifs <;> rfl
  · intro k
    unfold errorProbability
    have hV : (fun x : Messages m L × ℕ × ℕ => decide ((g62g_scheme m L hL).decode k x.2.1
        ((g62g_scheme m L hL).query k x.2.1)
        (fun n => observedAnswer (g62g_scheme m L hL) k n x) ≠ x.1 k)) = fun _ => false := by
      funext x
      obtain rfl := (hk k).symm
      simp only [decide_eq_false_iff_not, not_not]
      funext i
      simp [g62g_scheme, observedAnswer]
    rw [hV]
    simp
  · unfold WithinBudget
    rw [show (g62g_scheme m L hL).sharedSeed = PMF.pure 0 from rfl, g62g_ent_pure]
    exact zero_le
  · intro k
    obtain rfl := (hk k).symm
    unfold spirRate
    have : (0 : ℝ) < ((m.ell ⟨0, m.K_pos⟩ * L : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (m.ell_pos _) hL
    simp only [g62g_scheme]
    exact div_self this.ne'

def g62g_seq (m : SpirParameters) (hK1 : m.K = 1) : ReliableSequence m where
  length t := t + 1
  block t := g62g_scheme m (t + 1) (Nat.succ_pos t)
  grows := Filter.tendsto_add_atTop_nat 1
  privacy t := (g62g_scheme_ok m hK1 (t + 1) (Nat.succ_pos t) 0).1
  reliability k := by
    have : ∀ t, errorProbability (g62g_scheme m (t + 1) (Nat.succ_pos t)) k = 0 :=
      fun t => (g62g_scheme_ok m hK1 (t + 1) (Nat.succ_pos t) 0).2.1 k
    simp only [this]
    exact tendsto_const_nhds

theorem solution (m : SpirParameters) (hK : m.K = 1)
    (rho : ℝ) (hrho : 0 ≤ rho) :
    spirCapacity m rho = 1 ∧
      spirCapacityRegion m rho = {R | ∀ k, 0 ≤ R k ∧ R k ≤ 1} := by
  have hA : {R | SpirAchievable m rho R} = {R : Fin m.K → ℝ | ∀ k, 0 ≤ R k ∧ R k ≤ 1} := by
    ext R
    constructor
    · rintro ⟨hnn, a, -, hr⟩ k
      refine ⟨hnn k, ?_⟩
      have hev := (a.reliability k).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
      obtain ⟨t, ht⟩ := hev.exists
      have hD : m.ell k * a.length t ≤ (a.block t).download := by
        by_contra hlt
        rw [not_le] at hlt
        have h1 := g62g_conv (a.block t) hK k hlt
        have h2 : ((2 : ℝ≥0∞)⁻¹).toReal ≤ errorProbability (a.block t) k :=
          ENNReal.toReal_mono (PMF.apply_ne_top _ _) h1
        simp at h2
        linarith
      calc R k ≤ spirRate (a.block t) k := hr t k
        _ ≤ 1 := by
          unfold spirRate
          exact div_le_one_of_le₀ (by exact_mod_cast hD) (by positivity)
    · intro hR
      refine ⟨fun k => (hR k).1, g62g_seq m hK, fun t => ?_, fun t k => ?_⟩
      · exact (g62g_scheme_ok m hK (t + 1) (Nat.succ_pos t) rho).2.2.1
      · exact (hR k).2.trans
          (le_of_eq ((g62g_scheme_ok m hK (t + 1) (Nat.succ_pos t) rho).2.2.2 k).symm)
  have hclosed : IsClosed {R : Fin m.K → ℝ | ∀ k, 0 ≤ R k ∧ R k ≤ 1} := by
    have : {R : Fin m.K → ℝ | ∀ k, 0 ≤ R k ∧ R k ≤ 1} =
        ⋂ k, ({R : Fin m.K → ℝ | 0 ≤ R k} ∩ {R | R k ≤ 1}) := by
      ext R; simp [Set.mem_iInter]
    rw [this]
    exact isClosed_iInter (fun k => (isClosed_le continuous_const (continuous_apply k)).inter
      (isClosed_le (continuous_apply k) continuous_const))
  have hRg : spirCapacityRegion m rho = {R | ∀ k, 0 ≤ R k ∧ R k ≤ 1} := by
    unfold spirCapacityRegion
    rw [hA, Set.union_eq_right.mpr, hclosed.closure_eq]
    rw [Set.singleton_subset_iff]
    intro k
    simp
  refine ⟨?_, hRg⟩
  unfold spirCapacity
  apply le_antisymm
  · refine iSup_le fun r => ?_
    have h : (fun _ : Fin m.K => r.val) ∈ {R : Fin m.K → ℝ | ∀ k, 0 ≤ R k ∧ R k ≤ 1} :=
      hRg ▸ r.2.2
    exact ENNReal.ofReal_le_one.mpr (h ⟨0, by omega⟩).2
  · have h1 : (fun _ : Fin m.K => (1 : ℝ)) ∈ spirCapacityRegion m rho := by
      rw [hRg]; intro k; exact ⟨zero_le_one, le_rfl⟩
    refine le_trans (le_of_eq ?_) (le_iSup _ ⟨1, zero_le_one, h1⟩)
    simp
