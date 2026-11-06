-- Prove2me | solution 1 for OTDRO.Dual.dual_reformulation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:03:06.312524+00:00
-- url     : https://prove2.me/submissions/23cc84ee-a8d1-44c9-872f-0d788d99be7e

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting
import Definitions.Def_ModelRiskOT_Duality_primalValue
import Theorems.Thm_ModelRiskOT_Duality_theorem_1
import Theorems.Thm_OTDRO_Dual_sup_transport_eq_ellRob

open MeasureTheory

namespace OTDRORed

open OTDRO.Dual ModelRiskOT.Duality Matrix

/-- Adding a real constant commutes with suprema in `EReal`. -/
lemma coe_add_iSup {ι : Sort*} (r : ℝ) (g : ι → EReal) :
    (r : EReal) + ⨆ i, g i = ⨆ i, ((r : EReal) + g i) := by
  let e : EReal ≃ EReal :=
    { toFun := fun z => (r : EReal) + z
      invFun := fun z => z - r
      left_inv := fun z => by simp [EReal.add_sub_cancel_left]
      right_inv := fun z => by
        show (r : EReal) + (z - r) = z
        rw [add_comm]; exact EReal.sub_add_cancel }
  let o : EReal ≃o EReal := Equiv.toOrderIso e
    (fun a b h => by simpa [e] using add_le_add_right h (r : EReal))
    (fun a b h => by simpa [e] using EReal.sub_le_sub h le_rfl)
  exact o.map_iSup g

lemma toENNReal_coe_real (x : ℝ) : (x : EReal).toENNReal = ENNReal.ofReal x := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top x), EReal.toReal_coe]

lemma ofReal_eq_max (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
  rcases le_total x 0 with h | h
  · simp [max_eq_right h, ENNReal.ofReal_of_nonpos h]
  · simp [max_eq_left h]

lemma key_max (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- Pointwise identity behind `extIntegral_const_add`. -/
lemma pointwise_id (r : ℝ) (z : EReal) :
    ((r : EReal) + z).toENNReal + (-z).toENNReal + ENNReal.ofReal (-r) =
      z.toENNReal + (-((r : EReal) + z)).toENNReal + ENNReal.ofReal r := by
  induction z using EReal.rec with
  | bot => simp
  | top => simp
  | coe t =>
    rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_neg, toENNReal_coe_real, toENNReal_coe_real,
      toENNReal_coe_real, toENNReal_coe_real]
    rw [ofReal_eq_max (r + t), ofReal_eq_max (-t), ofReal_eq_max (-r), ofReal_eq_max t,
      ofReal_eq_max (-(r + t)), ofReal_eq_max r]
    rw [← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
      ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
      ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
      ← ENNReal.ofReal_add (by positivity) (le_max_right _ _)]
    congr 1
    linarith [key_max (r + t), key_max t, key_max r]

lemma neg_part_le (r : ℝ) (z : EReal) :
    (-((r : EReal) + z)).toENNReal ≤ (-z).toENNReal + ENNReal.ofReal (-r) := by
  induction z using EReal.rec with
  | bot => simp
  | top => simp
  | coe t =>
    rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_neg, toENNReal_coe_real, toENNReal_coe_real]
    exact (ENNReal.ofReal_le_ofReal (by linarith : -(r + t) ≤ -t + -r)).trans ENNReal.ofReal_add_le

lemma top_sub_ennreal (a : ENNReal) (ha : a ≠ ⊤) : ((⊤ : ENNReal) : EReal) - (a : EReal) = ⊤ := by
  lift a to NNReal using ha
  simp

/-- `∫ (r + φ) = r + ∫ φ` for the extended integral, for measurable `φ` with integrable
negative part, against a probability measure. -/
lemma extIntegral_const_add {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (r : ℝ) (φ : X → EReal) (hφ : Measurable φ)
    (hneg : ∫⁻ x, (-φ x).toENNReal ∂ν ≠ ⊤) :
    extIntegral ν (fun x => (r : EReal) + φ x) = (r : EReal) + extIntegral ν φ := by
  unfold extIntegral
  set P := ∫⁻ x, ((r : EReal) + φ x).toENNReal ∂ν with hP
  set N := ∫⁻ x, (-((r : EReal) + φ x)).toENNReal ∂ν with hN
  set p := ∫⁻ x, (φ x).toENNReal ∂ν with hp
  set n := ∫⁻ x, (-φ x).toENNReal ∂ν with hn
  have m1 : Measurable fun x => ((r : EReal) + φ x).toENNReal :=
    (measurable_const.add hφ).ereal_toENNReal
  have m2 : Measurable fun x => (-φ x).toENNReal := hφ.neg.ereal_toENNReal
  have m3 : Measurable fun x => (φ x).toENNReal := hφ.ereal_toENNReal
  have m4 : Measurable fun x => (-((r : EReal) + φ x)).toENNReal :=
    (measurable_const.add hφ).neg.ereal_toENNReal
  have heq : P + n + ENNReal.ofReal (-r) = p + N + ENNReal.ofReal r := by
    have := congrArg (fun g => ∫⁻ x, g x ∂ν) (funext fun x => pointwise_id r (φ x))
    simp only at this
    rw [lintegral_add_right _ measurable_const, lintegral_add_right _ measurable_const,
      lintegral_add_left m1, lintegral_add_left m3] at this
    simpa using this
  have hNlt : N ≠ ⊤ := by
    have : N ≤ n + ENNReal.ofReal (-r) := by
      calc N ≤ ∫⁻ x, ((-φ x).toENNReal + ENNReal.ofReal (-r)) ∂ν :=
            lintegral_mono fun x => neg_part_le r (φ x)
        _ = n + ENNReal.ofReal (-r) := by
            rw [lintegral_add_right _ measurable_const]; simp [hn]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hneg, ENNReal.ofReal_ne_top⟩) this
  by_cases hptop : p = ⊤
  · have hPtop : P = ⊤ := by
      by_contra hPne
      have : p + N + ENNReal.ofReal r = ⊤ := by rw [hptop]; simp
      rw [← heq] at this
      simp [hPne, hneg] at this
    rw [hPtop, hptop]
    rw [top_sub_ennreal N hNlt, top_sub_ennreal n hneg]; simp
  · have hPne : P ≠ ⊤ := by
      intro hPtop
      have : P + n + ENNReal.ofReal (-r) = ⊤ := by rw [hPtop]; simp
      rw [heq] at this
      simp [hptop, hNlt] at this
    have hr := congrArg ENNReal.toReal heq
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hPne, hneg⟩) ENNReal.ofReal_ne_top,
      ENNReal.toReal_add hPne hneg,
      ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hptop, hNlt⟩) ENNReal.ofReal_ne_top,
      ENNReal.toReal_add hptop hNlt] at hr
    have hr' : P.toReal - N.toReal = r + (p.toReal - n.toReal) := by
      rcases le_total r 0 with h | h
      · rw [ENNReal.toReal_ofReal (by linarith), ENNReal.ofReal_of_nonpos h, ENNReal.toReal_zero] at hr
        linarith
      · rw [ENNReal.toReal_ofReal h, ENNReal.ofReal_of_nonpos (by linarith), ENNReal.toReal_zero] at hr
        linarith
    rw [← ENNReal.ofReal_toReal hPne, ← ENNReal.ofReal_toReal hNlt, ← ENNReal.ofReal_toReal hptop,
      ← ENNReal.ofReal_toReal hneg]
    rw [EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
      EReal.coe_ennreal_ofReal]
    rw [max_eq_left ENNReal.toReal_nonneg, max_eq_left ENNReal.toReal_nonneg,
      max_eq_left ENNReal.toReal_nonneg, max_eq_left ENNReal.toReal_nonneg]
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, hr']

section Main

variable {d : ℕ}

lemma mahalCost_A1 (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hpd : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      mahalCost A p.1 p.2)) : AssumptionA1 (mahalCost A) := by
  have pos : ∀ x y : EuclideanSpace ℝ (Fin d), x ≠ y → 0 < mahalCost A x y := by
    intro x y hxy
    have hv : (x - y).ofLp ≠ 0 := by
      intro h0
      apply hxy
      have : x.ofLp = y.ofLp := by simpa [sub_eq_zero] using h0
      exact WithLp.ofLp_injective _ this
    have := (hpd x).dotProduct_mulVec_pos hv
    simpa [mahalCost] using this
  refine ⟨?_, hlsc, ?_⟩
  · intro x y
    by_cases h : x = y
    · subst h; simp [mahalCost]
    · exact (pos x y h).le
  · intro x y
    constructor
    · intro h
      by_contra hxy
      exact (pos x y hxy).ne' h
    · intro h; subst h; simp [mahalCost]

lemma usc_comp_inner (ℓ : ℝ → ℝ) (hℓ : UpperSemicontinuous ℓ) {Y : Type*} [TopologicalSpace Y]
    (g : Y → ℝ) (hg : Continuous g) : UpperSemicontinuous (fun y => ℓ (g y)) := by
  rw [upperSemicontinuous_iff_isOpen_preimage] at hℓ ⊢
  intro t
  exact (hℓ t).preimage hg

lemma usc_g (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      mahalCost A p.1 p.2))
    (ℓ : ℝ → ℝ) (hℓ : UpperSemicontinuous ℓ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ℓ (inner ℝ β p.2) - lam * mahalCost A p.1 p.2) := by
  have h1 : UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ℓ (inner ℝ β p.2)) := usc_comp_inner ℓ hℓ _ (by fun_prop)
  have h2 : UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      -(lam * mahalCost A p.1 p.2)) :=
    Continuous.comp_lowerSemicontinuous_antitone (g := fun z : ℝ => -(lam * z))
      (by fun_prop) hlsc (fun a b hab => by simp only; nlinarith)
  simpa [sub_eq_add_neg] using h1.add h2

lemma meas_sup (g : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (hg : UpperSemicontinuous g) :
    Measurable (fun x => ⨆ y, (g (x, y) : EReal)) := by
  apply measurable_of_Ioi
  intro t
  have hset : (fun x => ⨆ y, (g (x, y) : EReal)) ⁻¹' Set.Ioi t =
      ⋃ q : ℚ, ⋃ (_ : t < ((q : ℝ) : EReal)), ⋃ k : ℕ,
        Prod.fst '' (g ⁻¹' Set.Ici (q : ℝ) ∩ Metric.closedBall 0 k) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, lt_iSup_iff, Set.mem_iUnion, Set.mem_image,
      Set.mem_inter_iff, Set.mem_Ici, Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨q, htq, hqg⟩ := EReal.lt_iff_exists_rat_btwn.1 hy
      obtain ⟨k, hk⟩ := exists_nat_ge ‖(x, y)‖
      exact ⟨q, htq, k, (x, y), ⟨(EReal.coe_lt_coe_iff.1 hqg).le, hk⟩, rfl⟩
    · rintro ⟨q, htq, k, ⟨a, b⟩, ⟨hab, _⟩, rfl⟩
      exact ⟨b, htq.trans_le (EReal.coe_le_coe_iff.2 hab)⟩
  rw [hset]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun k => ?_
  exact (((isCompact_closedBall 0 (k : ℝ)).inter_left
    (hg.isClosed_preimage (q : ℝ))).image continuous_fst).isClosed.measurableSet

lemma phiLam_eq_sup (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (ℓ : ℝ → ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    phiLam (mahalCost A) (fun x => ℓ (inner ℝ β x)) lam =
      fun x => ⨆ y, ((ℓ (inner ℝ β y) - lam * mahalCost A x y : ℝ) : EReal) := by
  funext x
  simp [phiLam, phiLamOn]

lemma pointwise_ellRob (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hpd : ∀ x, (A x).PosDef) (ℓ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (hlam : 0 ≤ lam) (x : EuclideanSpace ℝ (Fin d)) :
    ((lam * δ : ℝ) : EReal) + phiLam (mahalCost A) (fun x => ℓ (inner ℝ β x)) lam x =
      ellRob ℓ A δ β (lam * Real.sqrt δ) x := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  rw [← sup_transport_eq_ellRob A x (hpd x) ℓ δ hδ β (lam * Real.sqrt δ) (by positivity),
    phiLam_eq_sup, coe_add_iSup]
  refine Eq.trans ((Equiv.addLeft x).iSup_comp
    (g := fun y => ((lam * δ : ℝ) : EReal) +
      ((ℓ (inner ℝ β y) - lam * mahalCost A x y : ℝ) : EReal))).symm ?_
  congr 1
  funext Δ
  rw [← EReal.coe_add]
  congr 1
  have hc : mahalCost A x (x + Δ) = dotProduct Δ.ofLp (A x *ᵥ Δ.ofLp) := by
    simp [mahalCost, Matrix.mulVec_neg]
  simp only [Equiv.coe_addLeft, hc]
  field_simp
  ring

lemma key_dualObj (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hpd : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      mahalCost A p.1 p.2))
    (ℓ : ℝ → ℝ) (hℓ : UpperSemicontinuous ℓ) (δ : ℝ) (hδ : 0 < δ)
    (β : EuclideanSpace ℝ (Fin d)) (hint : Integrable (fun x => ℓ (inner ℝ β x)) P0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (lam, phiLam (mahalCost A) (fun x => ℓ (inner ℝ β x)) lam) ∈
        dualFeasible (mahalCost A) (fun x => ℓ (inner ℝ β x)) Set.univ ∧
      dualObj P0 δ lam (phiLam (mahalCost A) (fun x => ℓ (inner ℝ β x)) lam) =
        fDelta P0 ℓ A δ β (lam * Real.sqrt δ) := by
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ℓ (inner ℝ β x) with hf
  set φ := phiLam (mahalCost A) f lam with hφ
  have hmeas : Measurable φ := by
    rw [hφ, phiLam_eq_sup]
    exact meas_sup (fun p => ℓ (inner ℝ β p.2) - lam * mahalCost A p.1 p.2)
      (usc_g A hlsc ℓ hℓ β lam hlam)
  have hge : ∀ x y, ((f y - lam * mahalCost A x y : ℝ) : EReal) ≤ φ x := by
    intro x y
    rw [hφ, phiLam_eq_sup]
    exact le_iSup (fun y => ((ℓ (inner ℝ β y) - lam * mahalCost A x y : ℝ) : EReal)) y
  have hc0 : ∀ x, mahalCost A x x = 0 := fun x => by simp [mahalCost]
  have hneg : ∫⁻ x, (-φ x).toENNReal ∂P0 ≠ ⊤ := by
    refine ne_top_of_le_ne_top hint.hasFiniteIntegral.ne ?_
    refine lintegral_mono fun x => ?_
    have h1 : (f x : EReal) ≤ φ x := by simpa [hc0] using hge x x
    calc (-φ x).toENNReal ≤ (-(f x : EReal)).toENNReal := EReal.toENNReal_le_toENNReal (by
            simpa using h1)
      _ = ENNReal.ofReal (-f x) := by rw [← EReal.coe_neg, toENNReal_coe_real]
      _ ≤ ‖f x‖ₑ := by
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
  refine ⟨⟨hlam, fun B hB p _ => (hmeas hB).nullMeasurableSet, ?_⟩, ?_⟩
  · intro x _ y _
    calc (f y : EReal) = ((f y - lam * mahalCost A x y : ℝ) : EReal) +
          ((lam * mahalCost A x y : ℝ) : EReal) := by rw [← EReal.coe_add]; congr 1; ring
      _ ≤ φ x + ((lam * mahalCost A x y : ℝ) : EReal) := by
          gcongr
          exact hge x y
  · unfold dualObj fDelta
    rw [← extIntegral_const_add P0 (lam * δ) φ hmeas hneg]
    congr 1
    funext x
    exact pointwise_ellRob A hpd ℓ δ hδ β lam hlam x

end Main

end OTDRORed

open OTDRO.Dual OTDRORed in
theorem solution {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (hℓ : UpperSemicontinuous ℓ)
    (δ : ℝ) (hδ : 0 < δ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (β : EuclideanSpace ℝ (Fin d)) (hβ : β ∈ B)
    (hint : Integrable (fun x => ℓ (inner ℝ β x)) P0) :
    ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A) (fun x => ℓ (inner ℝ β x)) P0 δ =
        ⨅ lam ∈ Set.Ici (0 : ℝ), OTDRO.Dual.fDelta P0 ℓ A δ β lam ∧
      ∃ lamStar : ℝ, 0 ≤ lamStar ∧
        OTDRO.Dual.fDelta P0 ℓ A δ β lamStar =
          ⨅ lam ∈ Set.Ici (0 : ℝ), OTDRO.Dual.fDelta P0 ℓ A δ β lam := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hf : UpperSemicontinuous (fun x => ℓ (inner ℝ β x)) :=
    usc_comp_inner ℓ hℓ _ (by fun_prop)
  obtain ⟨hIJ, ⟨lam0, hlam0, -, hopt⟩, -, -⟩ :=
    ModelRiskOT.Duality.theorem_1 P0 (mahalCost A) (mahalCost_A1 A hA.posDef hA.lsc)
      (fun x => ℓ (inner ℝ β x)) hf hint δ hδ
  have hle : ∀ lam' ∈ Set.Ici (0 : ℝ),
      ModelRiskOT.Duality.dualValue (mahalCost A) (fun x => ℓ (inner ℝ β x)) P0 δ ≤
        fDelta P0 ℓ A δ β lam' := by
    intro lam' hlam'
    have hl : 0 ≤ lam' / Real.sqrt δ := div_nonneg hlam' hs.le
    obtain ⟨hfeas, heq⟩ := key_dualObj P0 A hA.posDef hA.lsc ℓ hℓ δ hδ β hint _ hl
    have : lam' / Real.sqrt δ * Real.sqrt δ = lam' := by field_simp
    rw [this] at heq
    rw [← heq]
    unfold ModelRiskOT.Duality.dualValue
    exact iInf₂_le (_ : ℝ × (EuclideanSpace ℝ (Fin d) → EReal)) hfeas
  obtain ⟨-, heq0⟩ := key_dualObj P0 A hA.posDef hA.lsc ℓ hℓ δ hδ β hint lam0 hlam0
  have hinf : ModelRiskOT.Duality.dualValue (mahalCost A) (fun x => ℓ (inner ℝ β x)) P0 δ =
      ⨅ lam ∈ Set.Ici (0 : ℝ), fDelta P0 ℓ A δ β lam := by
    refine le_antisymm (le_iInf₂ hle) ?_
    calc ⨅ lam ∈ Set.Ici (0 : ℝ), fDelta P0 ℓ A δ β lam ≤ fDelta P0 ℓ A δ β (lam0 * Real.sqrt δ) :=
          iInf₂_le _ (Set.mem_Ici.2 (by positivity))
      _ = _ := by rw [← heq0, hopt]
  refine ⟨hIJ.trans hinf, lam0 * Real.sqrt δ, by positivity, ?_⟩
  rw [← heq0, hopt, hinf]
