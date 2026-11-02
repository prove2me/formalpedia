-- Prove2me | solution 1 for RankOneBimatrix.BinSearch.extreme_lambda_size
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:38:11.744183+00:00
-- url     : https://prove2.me/submissions/6602078a-ab61-4436-962f-2e727a989b4c

import Definitions.Def_RankOneBimatrix_BinSearch_Algorithm
open Matrix RankOneBimatrix.BinSearch Filter Topology

namespace R1BSELS


/-- (A) At an extreme point of `{w | ∀ k, G k ⬝ᵥ w ≤ h k}`, the tight rows have trivial
common kernel. -/
lemma ext_kernel {ι K : Type*} [Fintype ι] [Fintype K] (G : K → ι → ℝ) (h : K → ℝ)
    (z : ι → ℝ) (hz : z ∈ Set.extremePoints ℝ {w | ∀ k, G k ⬝ᵥ w ≤ h k}) (w : ι → ℝ)
    (hw : ∀ k, G k ⬝ᵥ z = h k → G k ⬝ᵥ w = 0) : w = 0 := by
  rw [mem_extremePoints] at hz
  obtain ⟨hzS, hext⟩ := hz
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ k, G k ⬝ᵥ z < h k → ε * |G k ⬝ᵥ w| < h k - G k ⬝ᵥ z := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : G k ⬝ᵥ z < h k
    · have ht : Tendsto (fun ε : ℝ => ε * |G k ⬝ᵥ w|) (𝓝[>] 0) (𝓝 (0 * |G k ⬝ᵥ w|)) :=
        ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
      rw [zero_mul] at ht
      filter_upwards [ht.eventually (gt_mem_nhds (sub_pos.2 hk))] with ε hε _ using hε
    · exact Eventually.of_forall fun ε h' => absurd h' hk
  obtain ⟨ε, hε, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hεpos : (0:ℝ) < ε := hεpos
  have hmem : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → z + (σ * ε) • w ∈ {w | ∀ k, G k ⬝ᵥ w ≤ h k} := by
    intro σ hσ k
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    by_cases hk : G k ⬝ᵥ z < h k
    · have h1 := hε k hk
      have h2 : σ * ε * (G k ⬝ᵥ w) ≤ ε * |G k ⬝ᵥ w| := by
        rcases hσ with rfl | rfl
        · nlinarith [le_abs_self (G k ⬝ᵥ w)]
        · nlinarith [neg_abs_le (G k ⬝ᵥ w)]
      linarith
    · have hk' : G k ⬝ᵥ z = h k := le_antisymm (hzS k) (not_lt.1 hk)
      rw [hw k hk', mul_zero, add_zero, hk']
  have hseg : z ∈ openSegment ℝ (z + ((-1) * ε) • w) (z + (1 * ε) • w) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have := (hext _ (hmem _ (Or.inr rfl)) _ (hmem _ (Or.inl rfl)) hseg).2
  have h0 : (1 * ε) • w = 0 := by
    have := congrArg (fun u => u - z) this
    simpa using this
  rw [one_mul] at h0
  exact (smul_eq_zero.1 h0).resolve_left hεpos.ne'



lemma rat_of_int_ratio (D1 D2 : ℤ) (hD2 : D2 ≠ 0) :
    ((D1 : ℚ) / D2).num.natAbs ≤ D1.natAbs ∧ ((D1 : ℚ) / D2).den ≤ D2.natAbs := by
  rw [← Rat.divInt_eq_div]
  constructor
  · by_cases hD1 : D1 = 0
    · subst hD1; simp
    · exact Nat.le_of_dvd (Int.natAbs_pos.2 hD1)
        (Int.natAbs_dvd_natAbs.2 (Rat.num_dvd D1 hD2))
  · exact Nat.le_of_dvd (Int.natAbs_pos.2 hD2) (Int.ofNat_dvd_left.1 (Rat.den_dvd D1 D2))

/-- (B) Cramer: a point that satisfies tight integer rows whose common kernel is trivial
has rational coordinates with bounded numerator and denominator. -/
lemma cramer_rat {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    (G : K → ι → ℤ) (h : K → ℤ) (U : ℕ) (hG : ∀ k i, |G k i| ≤ U) (hh : ∀ k, |h k| ≤ U)
    (T : K → Prop) [DecidablePred T] (z : ι → ℝ)
    (hzT : ∀ k, T k → (fun i => (G k i : ℝ)) ⬝ᵥ z = h k)
    (hker : ∀ w : ι → ℝ, (∀ k, T k → (fun i => (G k i : ℝ)) ⬝ᵥ w = 0) → w = 0) (i0 : ι) :
    ∃ q : ℚ, (q : ℝ) = z i0 ∧
      q.num.natAbs ≤ (Fintype.card ι).factorial * (Fintype.card K * U ^ 2) ^ Fintype.card ι ∧
      q.den ≤ (Fintype.card ι).factorial * (Fintype.card K * U ^ 2) ^ Fintype.card ι := by
  classical
  let Gt : Matrix K ι ℤ := fun k i => if T k then G k i else 0
  let ht : K → ℤ := fun k => if T k then h k else 0
  let N : Matrix ι ι ℤ := Gtᵀ * Gt
  let c : ι → ℤ := Gtᵀ *ᵥ ht
  let f := Int.castRingHom ℝ
  let Gr : Matrix K ι ℝ := fun k i => if T k then (G k i : ℝ) else 0
  have hGz : Gr *ᵥ z = fun k => ((ht k : ℤ) : ℝ) := by
    ext k
    by_cases hk : T k
    · have := hzT k hk
      simp only [dotProduct] at this
      simp only [Gr, ht, hk, if_true, mulVec, dotProduct]
      exact this
    · simp [Gr, ht, hk, mulVec, dotProduct]
  have hNr : N.map (Int.cast : ℤ → ℝ) = Grᵀ * Gr := by
    ext i j
    rw [Matrix.map_apply]
    show ((∑ k, Gtᵀ i k * Gt k j : ℤ) : ℝ) = ∑ k, Grᵀ i k * Gr k j
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [transpose_apply]
    simp only [Gt, Gr]
    split_ifs <;> simp
  have hNz : N.map (Int.cast : ℤ → ℝ) *ᵥ z = fun i => ((c i : ℤ) : ℝ) := by
    rw [hNr, ← mulVec_mulVec, hGz]
    ext i
    simp only [c, mulVec, dotProduct, Int.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [transpose_apply]
    simp only [Gt, Gr, ht]
    split_ifs <;> simp
  have hdet : (N.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hNw⟩ := (exists_mulVec_eq_zero_iff).2 h0
    have h1 : (Gr *ᵥ w) ⬝ᵥ (Gr *ᵥ w) = 0 := by
      have : w ⬝ᵥ ((Grᵀ * Gr) *ᵥ w) = 0 := by rw [← hNr, hNw, dotProduct_zero]
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at this
      exact this
    have h2 : Gr *ᵥ w = 0 := dotProduct_self_eq_zero.1 h1
    apply hw0
    apply hker w
    intro k hk
    have := congrFun h2 k
    simpa [Gr, hk, mulVec, dotProduct] using this
  -- Cramer
  set Nr := N.map (Int.cast : ℤ → ℝ) with hNrdef
  have hcr : Nr.det • z = Nr.cramer (fun i => ((c i : ℤ) : ℝ)) := by
    rw [cramer_eq_adjugate_mulVec, ← hNz, mulVec_mulVec, adjugate_mul, smul_mulVec,
      one_mulVec]
  have hc0 := congrFun hcr i0
  rw [cramer_apply, Pi.smul_apply, smul_eq_mul] at hc0
  have hupd : Nr.updateCol i0 (fun i => ((c i : ℤ) : ℝ)) =
      (N.updateCol i0 c).map (Int.cast : ℤ → ℝ) := by
    ext i j; simp only [updateCol_apply, map_apply, Nr]; split_ifs <;> rfl
  have hdetN : Nr.det = ((N.det : ℤ) : ℝ) := by
    rw [hNrdef]; exact ((Int.castRingHom ℝ).map_det N).symm
  have hdetU : (Nr.updateCol i0 (fun i => ((c i : ℤ) : ℝ))).det =
      (((N.updateCol i0 c).det : ℤ) : ℝ) := by
    rw [hupd]; exact ((Int.castRingHom ℝ).map_det _).symm
  rw [hdetU, hdetN] at hc0
  have hD2 : N.det ≠ 0 := by
    intro h0; apply hdet; rw [hdetN, h0, Int.cast_zero]
  obtain ⟨b1, b2⟩ := rat_of_int_ratio (N.updateCol i0 c).det N.det hD2
  have hGt : ∀ k i, |Gt k i| ≤ U := by
    intro k i; simp only [Gt]; split_ifs
    · exact hG k i
    · simp
  have hht : ∀ k, |ht k| ≤ U := by
    intro k; simp only [ht]; split_ifs
    · exact hh k
    · simp
  have hsum : ∀ (u v : K → ℤ), (∀ k, |u k| ≤ U) → (∀ k, |v k| ≤ U) →
      |∑ k, u k * v k| ≤ ((Fintype.card K * U ^ 2 : ℕ) : ℤ) := by
    intro u v hu hv
    calc |∑ k, u k * v k| ≤ ∑ k, |u k * v k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : K, (U : ℤ) * U := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]; exact mul_le_mul (hu k) (hv k) (abs_nonneg _) (by positivity)
      _ = _ := by simp [Finset.sum_const, Finset.card_univ, sq]
  have hNb : ∀ i j, |N i j| ≤ ((Fintype.card K * U ^ 2 : ℕ) : ℤ) := by
    intro i j
    show |∑ k, Gtᵀ i k * Gt k j| ≤ _
    simp only [transpose_apply]
    exact hsum _ _ (fun k => hGt k i) (fun k => hGt k j)
  have hcb : ∀ i, |c i| ≤ ((Fintype.card K * U ^ 2 : ℕ) : ℤ) := by
    intro i
    show |∑ k, Gtᵀ i k * ht k| ≤ _
    simp only [transpose_apply]
    exact hsum _ _ (fun k => hGt k i) hht
  have hUb : ∀ i j, |N.updateCol i0 c i j| ≤ ((Fintype.card K * U ^ 2 : ℕ) : ℤ) := by
    intro i j; rw [updateCol_apply]; split_ifs
    · exact hcb i
    · exact hNb i j
  have detb : ∀ M : Matrix ι ι ℤ, (∀ i j, |M i j| ≤ ((Fintype.card K * U ^ 2 : ℕ) : ℤ)) →
      M.det.natAbs ≤ (Fintype.card ι).factorial * (Fintype.card K * U ^ 2) ^ Fintype.card ι := by
    intro M hM
    have := Matrix.det_le (abv := AbsoluteValue.abs) hM
    simp only [AbsoluteValue.abs_apply, nsmul_eq_mul] at this
    have h2 : ((M.det.natAbs : ℕ) : ℤ) ≤
        (((Fintype.card ι).factorial * (Fintype.card K * U ^ 2) ^ Fintype.card ι : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]; push_cast at this ⊢; exact this
    exact_mod_cast h2
  refine ⟨((N.updateCol i0 c).det : ℚ) / N.det, ?_, ?_, ?_⟩
  · rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
    have : ((N.det : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hD2
    rw [eq_comm, eq_div_iff this]; linarith [hc0]
  · exact b1.trans (detb _ hUb)
  · exact b2.trans (detb _ hNb)



variable {m n : ℕ}

abbrev Idx (m n : ℕ) := (Fin m ⊕ Fin n) ⊕ Bool

def coord : PolyPoint m n ≃ₗ[ℝ] (Idx m n → ℝ) where
  toFun p := fun t => match t with
    | .inl (.inl i) => p.2.1 i
    | .inl (.inr j) => p.2.2.2 j
    | .inr true => p.1
    | .inr false => p.2.2.1
  invFun w := (w (.inr true), fun i => w (.inl (.inl i)), w (.inr false),
    fun j => w (.inl (.inr j)))
  map_add' p q := by ext t; rcases t with (i|j)|_|_ <;> rfl
  map_smul' r p := by ext t; rcases t with (i|j)|_|_ <;> rfl
  left_inv p := rfl
  right_inv w := by ext t; rcases t with (i|j)|_|_ <;> rfl

def blk (rx : Fin m → ℚ) (rs : Fin n → ℚ) (rl rv : ℚ) : Idx m n → ℚ := fun t =>
  match t with
  | .inl (.inl i) => rx i
  | .inl (.inr j) => rs j
  | .inr true => rl
  | .inr false => rv

def rdot (r : Idx m n → ℚ) (w : Idx m n → ℝ) : ℝ := ∑ t, (r t : ℝ) * w t

lemma rdot_blk (rx : Fin m → ℚ) (rs : Fin n → ℚ) (rl rv : ℚ) (p : PolyPoint m n) :
    rdot (blk rx rs rl rv) (coord p) = (∑ i, (rx i : ℝ) * p.2.1 i) +
      (∑ j, (rs j : ℝ) * p.2.2.2 j) + (rl : ℝ) * p.1 + (rv : ℝ) * p.2.2.1 := by
  simp only [rdot, Fintype.sum_sum_type, Fintype.sum_bool]
  simp only [blk, coord, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  ring

abbrev Kc (m n : ℕ) := (Fin m × Bool) ⊕ (Fin n × Bool × Bool) ⊕ (Bool × Bool)

/-- Rows of the constraint system; `mode = none` is `P(M,N)`, `some true` is `Pmax`,
`some false` is `Pmin`. -/
def row (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) (mode : Option Bool) : Kc m n → Idx m n → ℚ
  | .inl (i, false) => blk (-Pi.single i 1) 0 0 0
  | .inl (i, true) => blk (if i ∈ M then Pi.single i 1 else 0) 0 0 0
  | .inr (.inl (j, false, false)) => blk 0 (-Pi.single j 1) 0 0
  | .inr (.inl (j, false, true)) => blk 0 (if j ∈ N then Pi.single j 1 else 0) 0 0
  | .inr (.inl (j, true, false)) => blk (fun i => A i j) (-Pi.single j 1) (-b j) 1
  | .inr (.inl (j, true, true)) => blk (fun i => -A i j) (Pi.single j 1) (b j) (-1)
  | .inr (.inr (false, false)) => blk 1 0 0 0
  | .inr (.inr (false, true)) => blk (-1) 0 0 0
  | .inr (.inr (true, false)) => match mode with
    | none => blk 0 0 0 0
    | some true => blk (-a) 0 1 0
    | some false => blk a 0 (-1) 0
  | .inr (.inr (true, true)) => match mode with
    | none => blk 0 0 0 0
    | some true => blk 0 0 (-1) 0
    | some false => blk 0 0 1 0

def rhs (lam' : ℚ) (mode : Option Bool) : Kc m n → ℚ
  | .inr (.inr (false, false)) => 1
  | .inr (.inr (false, true)) => -1
  | .inr (.inr (true, true)) => match mode with
    | none => 0
    | some true => -lam'
    | some false => lam'
  | _ => 0

def Sset (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) (lam' : ℚ) : Option Bool → Set (PolyPoint m n)
  | none => PFace (A.map (fun r => (r : ℝ))) (fun j => (b j : ℝ)) M N
  | some true => PmaxFeas (A.map (fun r => (r : ℝ))) (fun i => (a i : ℝ)) (fun j => (b j : ℝ))
      M N (lam' : ℝ)
  | some false => PminFeas (A.map (fun r => (r : ℝ))) (fun i => (a i : ℝ)) (fun j => (b j : ℝ))
      M N (lam' : ℝ)

lemma sum_single_mul {k : ℕ} (i0 : Fin k) (x : Fin k → ℝ) :
    ∑ i, (((Pi.single i0 (1:ℚ) : Fin k → ℚ) i : ℚ) : ℝ) * x i = x i0 := by
  rw [Finset.sum_eq_single i0]
  · simp
  · intro j _ hj; simp [hj]
  · simp

lemma mem_Sset_iff (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) (lam' : ℚ) (mode : Option Bool)
    (p : PolyPoint m n) :
    p ∈ Sset A a b M N lam' mode ↔
      ∀ k, rdot (row A a b M N mode k) (coord p) ≤ (rhs lam' mode k : ℝ) := by
  obtain ⟨lam, x, v, s⟩ := p
  have hAT : ∀ j, ((A.map (fun r => (r:ℝ)))ᵀ *ᵥ x) j = ∑ i, (A i j : ℝ) * x i := by
    intro j; simp [mulVec, dotProduct, mul_comm]
  have hxa : x ⬝ᵥ (fun i => (a i : ℝ)) = ∑ i, (a i : ℝ) * x i := by
    simp [dotProduct, mul_comm]
  have v1 : ∀ i, rdot (row A a b M N mode (.inl (i, false))) (coord (lam, x, v, s)) = -x i := by
    intro i; simp [row, rdot_blk, sum_single_mul]
  have v2 : ∀ i, rdot (row A a b M N mode (.inl (i, true))) (coord (lam, x, v, s)) =
      if i ∈ M then x i else 0 := by
    intro i; split_ifs with h <;> simp [row, rdot_blk, sum_single_mul, h]
  have v3 : ∀ j, rdot (row A a b M N mode (.inr (.inl (j, false, false))))
      (coord (lam, x, v, s)) = -s j := by
    intro j; simp [row, rdot_blk, sum_single_mul]
  have v4 : ∀ j, rdot (row A a b M N mode (.inr (.inl (j, false, true))))
      (coord (lam, x, v, s)) = if j ∈ N then s j else 0 := by
    intro j; split_ifs with h <;> simp [row, rdot_blk, sum_single_mul, h]
  have v5 : ∀ j, rdot (row A a b M N mode (.inr (.inl (j, true, false))))
      (coord (lam, x, v, s)) = (∑ i, (A i j : ℝ) * x i) - s j - (b j : ℝ) * lam + v := by
    intro j; simp [row, rdot_blk, sum_single_mul]; ring
  have v6 : ∀ j, rdot (row A a b M N mode (.inr (.inl (j, true, true))))
      (coord (lam, x, v, s)) = -(∑ i, (A i j : ℝ) * x i) + s j + (b j : ℝ) * lam - v := by
    intro j; simp [row, rdot_blk, sum_single_mul]; ring
  have v7 : rdot (row A a b M N mode (.inr (.inr (false, false)))) (coord (lam, x, v, s)) =
      ∑ i, x i := by simp [row, rdot_blk]
  have v8 : rdot (row A a b M N mode (.inr (.inr (false, true)))) (coord (lam, x, v, s)) =
      -∑ i, x i := by simp [row, rdot_blk]
  have core : (lam, x, v, s) ∈ PFace (A.map (fun r => (r : ℝ))) (fun j => (b j : ℝ)) M N ↔
      (∀ i : Fin m, -x i ≤ 0 ∧ (if i ∈ M then x i else 0) ≤ 0) ∧
      (∀ j : Fin n, (-s j ≤ 0 ∧ (if j ∈ N then s j else 0) ≤ 0) ∧
          ∑ i, (A i j : ℝ) * x i - s j - (b j : ℝ) * lam + v ≤ 0 ∧
          -∑ i, (A i j : ℝ) * x i + s j + (b j : ℝ) * lam - v ≤ 0) ∧
        (∑ i, x i ≤ 1 ∧ -∑ i, x i ≤ -1) := by
    simp only [PFace, PPoly, PFeas, Set.mem_setOf_eq, hAT]
    constructor
    · rintro ⟨⟨⟨hx0, hsum⟩, hs0, heq⟩, hM, hN⟩
      refine ⟨fun i => ⟨by linarith [hx0 i], ?_⟩, fun j => ⟨⟨by linarith [hs0 j], ?_⟩,
        by linarith [heq j], by linarith [heq j]⟩, by simp only [hsum]; norm_num⟩
      · split_ifs with h
        · rw [hM i h]
        · exact le_refl _
      · split_ifs with h
        · rw [hN j h]
        · exact le_refl _
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨⟨⟨fun i => by linarith [(h1 i).1], by linarith⟩, fun j => by linarith [(h2 j).1.1],
        fun j => by linarith [(h2 j).2.1, (h2 j).2.2]⟩, fun i hi => ?_, fun j hj => ?_⟩
      · have := (h1 i).2; rw [if_pos hi] at this; linarith [(h1 i).1]
      · have := (h2 j).1.2; rw [if_pos hj] at this; linarith [(h2 j).1.1]
  rcases mode with _ | ⟨_ | _⟩
  · have v9 : rdot (row A a b M N none (.inr (.inr (true, false)))) (coord (lam, x, v, s)) = 0 := by
      simp [row, rdot_blk]
    have v10 : rdot (row A a b M N none (.inr (.inr (true, true)))) (coord (lam, x, v, s)) = 0 := by
      simp [row, rdot_blk]
    simp only [Sum.forall, Prod.forall, Bool.forall_bool, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10,
      rhs, Rat.cast_zero, Rat.cast_one, Rat.cast_neg, le_refl, and_true]
    rw [← core]; rfl
  · have v9 : rdot (row A a b M N (some false) (.inr (.inr (true, false))))
        (coord (lam, x, v, s)) = (∑ i, (a i : ℝ) * x i) - lam := by
      simp [row, rdot_blk]; ring
    have v10 : rdot (row A a b M N (some false) (.inr (.inr (true, true))))
        (coord (lam, x, v, s)) = lam := by
      simp [row, rdot_blk]
    simp only [Sum.forall, Prod.forall, Bool.forall_bool, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10,
      rhs, Rat.cast_zero, Rat.cast_one, Rat.cast_neg]
    simp only [Sset, PminFeas, Set.mem_setOf_eq, hxa]
    rw [core]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩; exact ⟨h1, h2, h3, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨h1, h2, h3⟩, by linarith, by linarith⟩
  · have v9 : rdot (row A a b M N (some true) (.inr (.inr (true, false))))
        (coord (lam, x, v, s)) = -(∑ i, (a i : ℝ) * x i) + lam := by
      simp [row, rdot_blk]
    have v10 : rdot (row A a b M N (some true) (.inr (.inr (true, true))))
        (coord (lam, x, v, s)) = -lam := by
      simp [row, rdot_blk]
    simp only [Sum.forall, Prod.forall, Bool.forall_bool, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10,
      rhs, Rat.cast_zero, Rat.cast_one, Rat.cast_neg]
    simp only [Sset, PmaxFeas, Set.mem_setOf_eq, hxa]
    rw [core]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩; exact ⟨h1, h2, h3, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨h1, h2, h3⟩, by linarith, by linarith⟩

def Good (D E : ℕ) (r : ℚ) : Prop := r.den ∣ D ∧ r.num.natAbs ≤ 2 ^ E

lemma good_zero (D E : ℕ) : Good D E 0 := ⟨by simp, by simp⟩
lemma good_one (D E : ℕ) : Good D E 1 := ⟨by simp, by simpa using Nat.one_le_two_pow⟩
lemma good_neg {D E : ℕ} {r : ℚ} (h : Good D E r) : Good D E (-r) :=
  ⟨by simpa [Rat.neg_den] using h.1, by simpa [Rat.num_neg] using h.2⟩
lemma good_single {D E k : ℕ} (i i' : Fin k) : Good D E ((Pi.single i (1:ℚ) : Fin k → ℚ) i') := by
  rw [Pi.single_apply]; split_ifs
  · exact good_one D E
  · exact good_zero D E

lemma good_blk {D E : ℕ} {rx : Fin m → ℚ} {rs : Fin n → ℚ} {rl rv : ℚ}
    (hx : ∀ i, Good D E (rx i)) (hs : ∀ j, Good D E (rs j)) (hl : Good D E rl)
    (hv : Good D E rv) (t : Idx m n) : Good D E (blk rx rs rl rv t) := by
  rcases t with (i|j)|_|_
  · exact hx i
  · exact hs j
  · exact hv
  · exact hl

lemma good_row {D E : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) (mode : Option Bool)
    (hA : ∀ i j, Good D E (A i j)) (ha : ∀ i, Good D E (a i)) (hb : ∀ j, Good D E (b j))
    (k : Kc m n) (t : Idx m n) : Good D E (row A a b M N mode k t) := by
  have g0 := good_zero D E
  have g1 := good_one D E
  have gs : ∀ {k : ℕ} (i : Fin k) (i' : Fin k), Good D E ((Pi.single i (1:ℚ) : Fin k → ℚ) i') :=
    fun i i' => good_single i i'
  rcases k with ⟨i, _ | _⟩ | ⟨j, _ | _, _ | _⟩ | ⟨_ | _, _ | _⟩
  · exact good_blk (fun i' => good_neg (gs _ _)) (fun _ => g0) g0 g0 t
  · refine good_blk (fun i' => ?_) (fun _ => g0) g0 g0 t
    split_ifs
    · exact gs _ _
    · exact g0
  · exact good_blk (fun _ => g0) (fun j' => good_neg (gs _ _)) g0 g0 t
  · refine good_blk (fun _ => g0) (fun j' => ?_) g0 g0 t
    split_ifs
    · exact gs _ _
    · exact g0
  · exact good_blk (fun i => hA i j) (fun j' => good_neg (gs _ _)) (good_neg (hb j)) g1 t
  · exact good_blk (fun i => good_neg (hA i j)) (fun j' => gs _ _) (hb j) (good_neg g1) t
  · exact good_blk (fun _ => g1) (fun _ => g0) g0 g0 t
  · exact good_blk (fun _ => good_neg g1) (fun _ => g0) g0 g0 t
  · rcases mode with _ | ⟨_ | _⟩
    · exact good_blk (fun _ => g0) (fun _ => g0) g0 g0 t
    · exact good_blk (fun i => ha i) (fun _ => g0) (good_neg g1) g0 t
    · exact good_blk (fun i => good_neg (ha i)) (fun _ => g0) g1 g0 t
  · rcases mode with _ | ⟨_ | _⟩
    · exact good_blk (fun _ => g0) (fun _ => g0) g0 g0 t
    · exact good_blk (fun _ => g0) (fun _ => g0) g1 g0 t
    · exact good_blk (fun _ => g0) (fun _ => g0) (good_neg g1) g0 t

lemma good_rhs {D E : ℕ} (lam' : ℚ) (mode : Option Bool) (hl : Good D E lam') (k : Kc m n) :
    Good D E (rhs lam' mode k) := by
  rcases k with ⟨i, _ | _⟩ | ⟨j, _ | _, _ | _⟩ | ⟨_ | _, _ | _⟩ <;>
    first
    | exact good_zero D E
    | exact good_one D E
    | exact good_neg (good_one D E)
    | (rcases mode with _ | ⟨_ | _⟩
       · exact good_zero D E
       · exact hl
       · exact good_neg hl)

def intScale (D : ℕ) (r : ℚ) : ℤ := r.num * ((D / r.den : ℕ) : ℤ)

lemma intScale_cast {D E : ℕ} {r : ℚ} (h : Good D E r) :
    ((intScale D r : ℤ) : ℝ) = (D : ℝ) * (r : ℝ) := by
  obtain ⟨c, hc⟩ := h.1
  have hr' : (r : ℝ) * r.den = r.num := by exact_mod_cast congrArg (Rat.cast : ℚ → ℝ) (Rat.mul_den_eq_num r)
  simp only [intScale]
  rw [hc, Nat.mul_div_cancel_left _ r.den_pos]
  push_cast
  rw [← hr']; ring

lemma intScale_abs {D E : ℕ} {r : ℚ} (h : Good D E r) :
    |intScale D r| ≤ ((2 ^ E * D : ℕ) : ℤ) := by
  have h1 : |r.num| ≤ ((2 ^ E : ℕ) : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h.2
  have h2 : |((D / r.den : ℕ) : ℤ)| ≤ (D : ℤ) := by
    rw [Int.abs_natCast]; exact_mod_cast Nat.div_le_self _ _
  simp only [intScale, abs_mul]
  push_cast
  exact mul_le_mul (by exact_mod_cast h1) h2 (by positivity) (by positivity)

lemma arith (d K E D : ℕ) (hd : d ≤ 2 * E + 2) (hK : K ≤ 6 * E + 4) (hD : D ≤ 2 ^ E) :
    d.factorial * (K * (2 ^ E * D) ^ 2) ^ d ≤ 2 ^ (24 * (E + 1) ^ 2) := by
  have h1 : d.factorial ≤ (2 ^ d) ^ d :=
    (Nat.factorial_le_pow d).trans (Nat.pow_le_pow_left Nat.lt_two_pow_self.le d)
  have h2 : K * (2 ^ E * D) ^ 2 ≤ 2 ^ K * 2 ^ (4 * E) := by
    apply Nat.mul_le_mul Nat.lt_two_pow_self.le
    calc (2 ^ E * D) ^ 2 ≤ (2 ^ E * 2 ^ E) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_mul le_rfl hD) 2
      _ = 2 ^ (4 * E) := by rw [← pow_add, ← pow_mul]; ring_nf
  calc d.factorial * (K * (2 ^ E * D) ^ 2) ^ d ≤ (2 ^ d) ^ d * (2 ^ K * 2 ^ (4 * E)) ^ d :=
        Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 d)
    _ = 2 ^ (d * d + (K + 4 * E) * d) := by
        rw [← pow_add, ← pow_mul, ← pow_mul, ← pow_add]
    _ ≤ 2 ^ (24 * (E + 1) ^ 2) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have : (K + 4 * E) * d ≤ (10 * E + 4) * (2 * E + 2) := Nat.mul_le_mul (by omega) hd
        have : d * d ≤ (2 * E + 2) * (2 * E + 2) := Nat.mul_le_mul hd hd
        nlinarith

lemma size_bound {q : ℚ} {B X : ℕ} (hB : B ≤ 2 ^ X) (hn : q.num.natAbs ≤ B) (hd : q.den ≤ B) :
    ratSize q ≤ 2 * X + 3 := by
  have hs : ∀ k, k ≤ B → Nat.size k ≤ X + 1 := fun k hk =>
    Nat.size_le.2 (lt_of_le_of_lt (hk.trans hB) (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  have := hs _ hn; have := hs _ hd
  unfold ratSize; omega

lemma ratSize_ge (r : ℚ) : 1 ≤ ratSize r := by unfold ratSize; omega

lemma den_le (r : ℚ) : r.den ≤ 2 ^ ratSize r :=
  (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by norm_num) (by unfold ratSize; omega))

lemma num_le (r : ℚ) : r.num.natAbs ≤ 2 ^ ratSize r :=
  (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by norm_num) (by unfold ratSize; omega))

def Dv (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ) (lam' : ℚ) : ℕ :=
  (∏ i, ∏ j, (A i j).den) * (∏ i, (a i).den) * (∏ j, (b j).den) * lam'.den

lemma prod_den_le {ι : Type*} [Fintype ι] (f : ι → ℚ) :
    ∏ i, (f i).den ≤ 2 ^ ∑ i, ratSize (f i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => den_le (f i))

lemma Dv_le (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ) (lam' : ℚ) :
    Dv A a b lam' ≤ 2 ^ (inputSize A a b + ratSize lam') := by
  have h1 : ∏ i, ∏ j, (A i j).den ≤ 2 ^ ∑ i, ∑ j, ratSize (A i j) := by
    calc ∏ i, ∏ j, (A i j).den ≤ ∏ i, 2 ^ ∑ j, ratSize (A i j) :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => prod_den_le (A i))
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  unfold Dv inputSize
  rw [pow_add, pow_add, pow_add]
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 (prod_den_le a)) (prod_den_le b))
    (den_le lam')

lemma Dv_pos (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ) (lam' : ℚ) :
    0 < Dv A a b lam' := by
  unfold Dv
  have := fun (f : Fin n → ℚ) => Finset.prod_pos (s := Finset.univ) (fun j _ => (f j).den_pos)
  have := fun (f : Fin m → ℚ) => Finset.prod_pos (s := Finset.univ) (fun j _ => (f j).den_pos)
  have h1 : 0 < ∏ i, ∏ j, (A i j).den :=
    Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ => (A i j).den_pos))
  have := lam'.den_pos
  positivity

lemma goods (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ) (lam' : ℚ) :
    let D := Dv A a b lam'
    let E := inputSize A a b + ratSize lam'
    (∀ i j, Good D E (A i j)) ∧ (∀ i, Good D E (a i)) ∧ (∀ j, Good D E (b j)) ∧
      Good D E lam' := by
  intro D E
  have hp : ∀ r : ℚ, ratSize r ≤ E → r.num.natAbs ≤ 2 ^ E := fun r h =>
    (num_le r).trans (Nat.pow_le_pow_right (by norm_num) h)
  have hP1 : (∏ i, ∏ j, (A i j).den) ∣ D := by
    simp only [D, Dv]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  have hP2 : (∏ i, (a i).den) ∣ D := by
    simp only [D, Dv]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  have hP3 : (∏ j, (b j).den) ∣ D := by
    simp only [D, Dv]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hE1 : ∀ i j, ratSize (A i j) ≤ E := by
    intro i j
    have h1 : ratSize (A i j) ≤ ∑ j, ratSize (A i j) :=
      Finset.single_le_sum (f := fun j => ratSize (A i j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have h2 : ∑ j, ratSize (A i j) ≤ ∑ i, ∑ j, ratSize (A i j) :=
      Finset.single_le_sum (f := fun i => ∑ j, ratSize (A i j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    simp only [E, inputSize]; omega
  have hE2 : ∀ i, ratSize (a i) ≤ E := by
    intro i
    have h1 : ratSize (a i) ≤ ∑ i, ratSize (a i) :=
      Finset.single_le_sum (f := fun i => ratSize (a i)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    simp only [E, inputSize]; omega
  have hE3 : ∀ j, ratSize (b j) ≤ E := by
    intro j
    have h1 : ratSize (b j) ≤ ∑ j, ratSize (b j) :=
      Finset.single_le_sum (f := fun j => ratSize (b j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    simp only [E, inputSize]; omega
  refine ⟨fun i j => ⟨?_, hp _ (hE1 i j)⟩, fun i => ⟨?_, hp _ (hE2 i)⟩,
    fun j => ⟨?_, hp _ (hE3 j)⟩, ⟨?_, hp _ (by simp only [E]; omega)⟩⟩
  · exact dvd_trans (Finset.dvd_prod_of_mem (fun j => (A i j).den) (Finset.mem_univ j))
      (dvd_trans (Finset.dvd_prod_of_mem (fun i => ∏ j, (A i j).den) (Finset.mem_univ i)) hP1)
  · exact dvd_trans (Finset.dvd_prod_of_mem (fun i => (a i).den) (Finset.mem_univ i)) hP2
  · exact dvd_trans (Finset.dvd_prod_of_mem (fun j => (b j).den) (Finset.mem_univ j)) hP3
  · simp only [D, Dv]; exact dvd_mul_left _ _

lemma m_le (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ) :
    m ≤ inputSize A a b ∧ n ≤ inputSize A a b := by
  have h1 : ∑ _i : Fin m, 1 ≤ ∑ i, ratSize (a i) := Finset.sum_le_sum fun i _ => ratSize_ge _
  have h2 : ∑ _j : Fin n, 1 ≤ ∑ j, ratSize (b j) := Finset.sum_le_sum fun j _ => ratSize_ge _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1 h2
  unfold inputSize; omega


lemma key (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) (lam' : ℚ) (mode : Option Bool)
    (z : PolyPoint m n) (hz : z ∈ Set.extremePoints ℝ (Sset A a b M N lam' mode)) :
    ∃ q : ℚ, (q : ℝ) = z.1 ∧ ratSize q ≤ 51 * (inputSize A a b + ratSize lam' + 1) ^ 2 := by
  classical
  set E := inputSize A a b + ratSize lam' with hE
  set D := Dv A a b lam' with hDdef
  obtain ⟨gA, ga, gb, gl⟩ := goods A a b lam'
  let R : Kc m n → Idx m n → ℝ := fun k t => ((row A a b M N mode k t : ℚ) : ℝ)
  let c : Kc m n → ℝ := fun k => ((rhs lam' mode k : ℚ) : ℝ)
  have hS : coord '' Sset A a b M N lam' mode = {w | ∀ k, R k ⬝ᵥ w ≤ c k} := by
    ext w
    rw [LinearEquiv.image_eq_preimage_symm]
    simp only [Set.mem_preimage, mem_Sset_iff, LinearEquiv.apply_symm_apply, Set.mem_setOf_eq]
    rfl
  have hz' : coord z ∈ Set.extremePoints ℝ {w | ∀ k, R k ⬝ᵥ w ≤ c k} := by
    rw [← hS, ← image_extremePoints]; exact ⟨z, hz, rfl⟩
  have hker := ext_kernel R c (coord z) hz'
  let G : Kc m n → Idx m n → ℤ := fun k t => intScale D (row A a b M N mode k t)
  let H : Kc m n → ℤ := fun k => intScale D (rhs lam' mode k)
  have hGc : ∀ k w, (fun t => (G k t : ℝ)) ⬝ᵥ w = (D : ℝ) * (R k ⬝ᵥ w) := by
    intro k w
    simp only [G, R, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [intScale_cast (good_row A a b M N mode gA ga gb k t)]; ring
  have hHc : ∀ k, (H k : ℝ) = (D : ℝ) * c k := fun k => intScale_cast (good_rhs lam' mode gl k)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Dv_pos A a b lam'
  obtain ⟨q, hq, hnum, hden⟩ := cramer_rat G H (2 ^ E * D)
    (fun k t => intScale_abs (good_row A a b M N mode gA ga gb k t))
    (fun k => intScale_abs (good_rhs lam' mode gl k))
    (fun k => R k ⬝ᵥ coord z = c k) (coord z)
    (fun k hk => by rw [hGc, hHc, hk])
    (fun w hw => hker w fun k hk => by
      have := hw k hk
      rw [hGc] at this
      exact (mul_eq_zero.1 this).resolve_left hDpos.ne')
    (Sum.inr true)
  refine ⟨q, hq, ?_⟩
  have hmn := m_le A a b
  have hcI : Fintype.card (Idx m n) = m + n + 2 := by simp [Idx]
  have hcK : Fintype.card (Kc m n) = m * 2 + n * (2 * 2) + 2 * 2 := by simp [Kc]; omega
  rw [hcI, hcK] at hnum hden
  have hB := arith (m + n + 2) (m * 2 + n * (2 * 2) + 2 * 2) E D (by omega) (by omega)
    (Dv_le A a b lam')
  have := size_bound hB hnum hden
  have hY : 1 ≤ (E + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  generalize (E + 1) ^ 2 = Y at *
  omega

end R1BSELS

open R1BSELS in
theorem solution :
    ∃ p : Polynomial ℕ,
      ∀ (m n : ℕ), 0 < m → 0 < n →
      ∀ (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ)
        (M : Finset (Fin m)) (N : Finset (Fin n)) (lam' : ℚ),
        (∀ z ∈ Set.extremePoints ℝ (PFace (A.map (fun r => (r : ℝ)))
            (fun j => (b j : ℝ)) M N),
          ∃ q : ℚ, (q : ℝ) = z.1 ∧ ratSize q ≤ p.eval (inputSize A a b)) ∧
        (∀ z ∈ Set.extremePoints ℝ (PmaxFeas (A.map (fun r => (r : ℝ)))
            (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) M N (lam' : ℝ)),
          ∃ q : ℚ, (q : ℝ) = z.1 ∧
            ratSize q ≤ p.eval (inputSize A a b + ratSize lam')) ∧
        (∀ z ∈ Set.extremePoints ℝ (PminFeas (A.map (fun r => (r : ℝ)))
            (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) M N (lam' : ℝ)),
          ∃ q : ℚ, (q : ℝ) = z.1 ∧
            ratSize q ≤ p.eval (inputSize A a b + ratSize lam')) := by
  refine ⟨51 * (Polynomial.X + 3) ^ 2, fun m n _ _ A a b M N lam' => ⟨?_, ?_, ?_⟩⟩
  · intro z hz
    obtain ⟨q, hq, hs⟩ := key A a b M N 0 none z hz
    have h0 : ratSize 0 = 2 := by decide
    refine ⟨q, hq, ?_⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    rw [h0] at hs
    simpa [add_assoc] using hs
  · intro z hz
    obtain ⟨q, hq, hs⟩ := key A a b M N lam' (some true) z hz
    refine ⟨q, hq, ?_⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    exact hs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  · intro z hz
    obtain ⟨q, hq, hs⟩ := key A a b M N lam' (some false) z hz
    refine ⟨q, hq, ?_⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    exact hs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
