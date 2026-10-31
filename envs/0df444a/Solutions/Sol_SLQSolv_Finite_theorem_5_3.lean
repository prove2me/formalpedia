-- Prove2me | solution 1 for SLQSolv.Finite.theorem_5_3
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T13:40:55.779048+00:00
-- url     : https://prove2.me/submissions/b05e47d8-04be-4607-9d61-936c6349683b

import Mathlib
import Definitions.Def_SLQSolv_Finite_Comparison
import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped NNReal Matrix

namespace SLQCex9ca7

open SLQSolv.Finite ProbabilityTheory

/-! ### A non-Borel set of times after the horizon -/

theorem exists_not_measurableSet_real : ∃ S : Set ℝ, ¬ MeasurableSet S := by
  by_contra h
  push Not at h
  set s : Set (Set ℝ) := ⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) (b : ℝ)} with hs_def
  have hcount : s.Countable :=
    Set.countable_iUnion fun _ => Set.countable_iUnion fun _ =>
      Set.countable_iUnion fun _ => Set.countable_singleton _
  have hs : Cardinal.mk s ≤ Cardinal.continuum :=
    (Cardinal.mk_le_aleph0_iff.mpr hcount.to_subtype).trans Cardinal.aleph0_le_continuum
  have hle := MeasurableSpace.cardinal_measurableSet_le_continuum hs
  have hm : ∀ t : Set ℝ, MeasurableSet[MeasurableSpace.generateFrom s] t := by
    intro t
    rw [hs_def, ← Real.borel_eq_generateFrom_Ioo_rat]
    exact h t
  have hinj : Cardinal.mk (Set ℝ) ≤
      Cardinal.mk {t | MeasurableSet[MeasurableSpace.generateFrom s] t} :=
    Cardinal.mk_le_of_injective
      (f := fun t : Set ℝ => (⟨t, hm t⟩ : {t | MeasurableSet[MeasurableSpace.generateFrom s] t}))
      (fun a b hab => congrArg Subtype.val hab)
  have h2 := hinj.trans hle
  rw [Cardinal.mk_set, Cardinal.mk_real] at h2
  exact absurd h2 (not_le.mpr (Cardinal.cantor _))

noncomputable def phi (x : ℝ) : ℝ≥0 := ⟨Real.exp x + 1, by positivity⟩

theorem phi_measurable : Measurable phi := by
  unfold phi
  exact (Real.measurable_exp.add_const 1).subtype_mk

theorem phi_injective : Function.Injective phi := by
  intro a b h
  have h' : Real.exp a + 1 = Real.exp b + 1 := congrArg Subtype.val h
  exact Real.exp_injective (by linarith)

theorem exists_bad : ∃ N : Set ℝ≥0, ¬ MeasurableSet N ∧ ∀ s ∈ N, 1 < s := by
  obtain ⟨S, hS⟩ := exists_not_measurableSet_real
  refine ⟨phi '' S, fun hN => hS ?_, ?_⟩
  · have h := phi_measurable hN
    rwa [Set.preimage_image_eq S phi_injective] at h
  · rintro s ⟨x, -, rfl⟩
    rw [← NNReal.coe_lt_coe]
    show (1 : ℝ) < Real.exp x + 1
    linarith [Real.exp_pos x]

/-! ### A Brownian motion -/

theorem brownian_isBrownianReal : IsBrownianReal brownian gaussianLimit := by
  have h := isPreBrownianReal_preBrownian
  have hs := h.exists_continuous_modification.choose_spec
  have hb : brownian = h.exists_continuous_modification.choose := rfl
  rw [hb]
  refine ⟨h.congr fun t => (hs.2.1 t).symm, ae_of_all _ fun ω => ?_⟩
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hbdd : BddAbove (Set.range fun n : ℕ => (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [div_le_one (by positivity)]
    push_cast
    linarith
  have hβ : ((1 / 4 : ℝ≥0) : ℝ) < ⨆ n : ℕ, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)) := by
    refine lt_of_lt_of_le ?_ (le_ciSup hbdd 1)
    push_cast
    norm_num
  obtain ⟨U, hU, C, hC⟩ := hs.2.2 ω t (1 / 4) (by norm_num) hβ
  exact (hC.continuousOn (by norm_num)).continuousAt hU

theorem isStdBrownian_cex :
    Peng1990.SMP.IsStdBrownian gaussianLimit (fun t ω (_ : Fin 1) => brownian t ω) where
  meas t := measurable_pi_lambda _ fun _ =>
    (isPreBrownianReal_preBrownian.exists_continuous_modification.choose_spec.1 t :
      Measurable (brownian t))
  brownian _ := brownian_isBrownianReal
  indep := iIndepFun.of_subsingleton

noncomputable def cexBasis : Basis (ℝ≥0 → ℝ) where
  P := gaussianLimit
  W := fun t ω _ => brownian t ω
  prob := inferInstance
  hW := isStdBrownian_cex

/-! ### The data -/

noncomputable def cexD (N : Set ℝ≥0) : ℝ≥0 → Matrix (Fin 1) (Fin 1) ℝ :=
  fun s => Matrix.of fun _ _ => N.indicator (fun _ => (1 : ℝ)) s

noncomputable def cexData (N : Set ℝ≥0) : Data (ℝ≥0 → ℝ) 1 1 where
  T := 1
  A := fun _ => 0
  B := fun _ => 0
  C := fun _ => 0
  D := cexD N
  b := 0
  σ := 0
  Q := fun _ => 0
  S := fun _ => 0
  R := fun _ => 1
  q := 0
  ρ := 0
  G := 1
  g := 0

theorem cexD_eq_zero (N : Set ℝ≥0) (hN : ∀ s ∈ N, 1 < s) (s : ℝ≥0) (hs : s ≤ 1) :
    cexD N s = 0 := by
  have hsN : s ∉ N := fun h => absurd hs (not_le.mpr (hN s h))
  ext i j
  simp [cexD, hsN]

theorem cexD_eq_zero_real (N : Set ℝ≥0) (hN : ∀ s ∈ N, 1 < s) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    cexD N s.toNNReal = 0 :=
  cexD_eq_zero N hN _ (Real.toNNReal_le_iff_le_coe.mpr (by simpa using hs.2))

theorem cost_nonneg (N : Set ℝ≥0) (Bs : Basis (ℝ≥0 → ℝ)) (t : ℝ≥0)
    (u : ℝ≥0 → (ℝ≥0 → ℝ) → Fin 1 → ℝ) (X : ℝ≥0 → (ℝ≥0 → ℝ) → Fin 1 → ℝ) :
    0 ≤ costAlong Bs (cexData N).hom t u X := by
  unfold costAlong
  apply integral_nonneg
  intro ω
  simp only [Data.hom, cexData, Matrix.one_mulVec, Matrix.zero_mulVec, Pi.zero_apply,
    zero_dotProduct, dotProduct_zero, mul_zero, add_zero, zero_add]
  apply add_nonneg
  · simp [dotProduct, Fin.sum_univ_one, mul_self_nonneg]
  · apply integral_nonneg
    intro s
    simp [dotProduct, Fin.sum_univ_one, mul_self_nonneg]

theorem J_nonneg (N : Set ℝ≥0) (t : ℝ≥0) (x : Fin 1 → ℝ) (u : ℝ≥0 → (ℝ≥0 → ℝ) → Fin 1 → ℝ) :
    0 ≤ J cexBasis (cexData N).hom t x u :=
  cost_nonneg N _ t u _

theorem h1_cex (N : Set ℝ≥0) (hN : ∀ s ∈ N, 1 < s) : H1 cexBasis (cexData N) where
  T_pos := by show (0 : ℝ≥0) < 1; exact one_pos
  A := fun i j => by simp [cexData]
  B := fun i j => by simp [cexData]
  C := fun i j => by simp [cexData]
  D := fun i j => by
    refine (memLp_top_const (0 : ℝ)).ae_eq ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    show (0 : ℝ) = cexD N s.toNNReal i j
    rw [cexD_eq_zero_real N hN s (by simpa [cexData] using hs)]
    rfl
  b := ⟨isStronglyProgressive_const _ (0 : Fin 1 → ℝ), by simp [cexData]⟩
  σ := ⟨isStronglyProgressive_const _ (0 : Fin 1 → ℝ), by simp [cexData]⟩

theorem h2_cex (N : Set ℝ≥0) : H2 cexBasis (cexData N) where
  Q := fun i j => by simp [cexData]
  S := fun i j => by simp [cexData]
  R := fun i j => memLp_top_const _
  Q_symm := fun _ => Matrix.isSymm_zero
  R_symm := fun _ => Matrix.isSymm_one
  q := ⟨isStronglyProgressive_const _ (0 : Fin 1 → ℝ), by simp [cexData]⟩
  ρ := ⟨isStronglyProgressive_const _ (0 : Fin 1 → ℝ), by simp [cexData]⟩
  G_symm := Matrix.isSymm_one
  g_meas := stronglyMeasurable_const
  g_sq := by simp [cexData]

theorem h56_cex (N : Set ℝ≥0) : IsNonnegJ0 cexBasis (cexData N) 0 :=
  fun u _ => J_nonneg N 0 0 u

theorem ric_zero (N : Set ℝ≥0) (ε : ℝ) (s : ℝ≥0) :
    riccatiRhs ((cexData N).addR ε) (fun _ => 1) s = 0 := by
  simp [riccatiRhs, gainK, Data.addR, cexData]

theorem hPe_cex (N : Set ℝ≥0) (hN : ∀ s ∈ N, 1 < s) :
    ∀ ε > 0, IsStronglyRegular ((cexData N).addR ε) ((fun _ _ => 1 : ℝ → ℝ≥0 → Matrix (Fin 1) (Fin 1) ℝ) ε) := by
  intro ε hε
  refine ⟨⟨continuousOn_const, fun _ _ _ => Matrix.isSymm_one, fun i j => ?_, fun t _ _ i j => ?_⟩,
    ε, hε, ?_⟩
  · simp [ric_zero]
  · simp only [ric_zero]
    simp [Data.addR, cexData]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hD := cexD_eq_zero_real N hN s (by simpa [cexData, Data.addR] using hs)
    simp [sigmaR, Data.addR, cexData, hD]
    exact Matrix.PosSemidef.one

theorem hM0_cex (N : Set ℝ≥0) :
    IsLyapunovSol (cexData N) 0 (fun _ => 1) where
  cont := continuousOn_const
  symm := fun _ _ => Matrix.isSymm_one
  integrable := fun i j => by simp [lyapunovRhs, cexData]
  eq := fun t _ i j => by simp [lyapunovRhs, cexData]

theorem hPhi_cex (N : Set ℝ≥0) : IsFundSolA (cexData N) (fun _ => 1) := by
  refine ⟨continuousOn_const, fun i j => by simp [cexData], fun t _ => ?_⟩
  ext i j
  simp [matInt, cexData]

theorem isFinite_cex (N : Set ℝ≥0) : IsFinite cexBasis (cexData N).hom := by
  intro t _ x
  refine lt_of_lt_of_le EReal.bot_lt_zero ?_
  unfold V
  exact le_iInf fun u => EReal.coe_nonneg.mpr (J_nonneg N t x u.1)

/-! ### No state exists from time `T = 1` for the constant control -/

theorem no_state (N : Set ℝ≥0) (hNm : ¬ MeasurableSet N) (hN : ∀ s ∈ N, 1 < s)
    (x : Fin 1 → ℝ) :
    ¬ ∃ X, IsState cexBasis (cexData N).hom 1 x (fun _ _ _ => 1) X := by
  rintro ⟨X, hX, -, -⟩
  obtain ⟨-, -, Jx, hJ, -⟩ := hX
  have hL := (hJ 0 0).1.1
  apply hNm
  have key : ∀ t : ℝ≥0, MeasurableSet (Iic t ∩ N) := by
    intro t
    have hm := ((hL t).measurable).comp (measurable_prodMk_right (y := (0 : ℝ≥0 → ℝ)))
    have hpre := hm (measurableSet_singleton (1 : ℝ))
    have hset : ((fun p : Iic t × (ℝ≥0 → ℝ) =>
        (if (1 : ℝ≥0) ≤ (p.1 : ℝ≥0) then
          (cexData N).hom.C p.1 *ᵥ X p.1 p.2 + (cexData N).hom.D p.1 *ᵥ (fun _ => (1 : ℝ))
            + (cexData N).hom.σ p.1 p.2
        else 0) 0) ∘ fun s : Iic t => (s, (0 : ℝ≥0 → ℝ))) ⁻¹' {1}
        = Subtype.val ⁻¹' N := by
      ext ⟨s, hs⟩
      by_cases hsN : s ∈ N
      · have h1s : (1 : ℝ≥0) ≤ s := (hN s hsN).le
        simp [Data.hom, cexData, cexD, hsN, h1s, Matrix.mulVec, dotProduct]
      · simp [Data.hom, cexData, cexD, hsN, Matrix.mulVec, dotProduct]
        split_ifs <;> simp [Matrix.mulVec, dotProduct]
    have hpre' : MeasurableSet (Subtype.val ⁻¹' N : Set (Iic t)) := by
      rw [← hset]; exact hpre
    have := MeasurableSet.subtype_image measurableSet_Iic hpre'
    rwa [Subtype.image_preimage_coe] at this
  have hU : N = ⋃ k : ℕ, (Iic (k : ℝ≥0) ∩ N) := by
    ext s
    simp only [mem_iUnion, mem_inter_iff, mem_Iic]
    constructor
    · intro hs
      obtain ⟨k, hk⟩ := exists_nat_ge s
      exact ⟨k, hk, hs⟩
    · rintro ⟨_, _, hs⟩
      exact hs
  rw [hU]
  exact MeasurableSet.iUnion fun k => key k

theorem V0_le_zero (N : Set ℝ≥0) (hNm : ¬ MeasurableSet N) (hN : ∀ s ∈ N, 1 < s)
    (x : Fin 1 → ℝ) : V0 cexBasis (cexData N) 1 x ≤ 0 := by
  have hadm : Adm cexBasis (cexData N).hom 1 (fun _ _ _ => 1) := by
    refine ⟨isStronglyProgressive_const _ (fun _ => (1 : ℝ)), ?_⟩
    simp [Data.hom, cexData, Measure.restrict_singleton]
  have hst : state cexBasis (cexData N).hom 1 x (fun _ _ _ => 1) = 0 := by
    unfold state
    rw [dif_neg (no_state N hNm hN x)]
  unfold V0 V
  refine (iInf_le _ ⟨fun _ _ _ => 1, hadm⟩).trans ?_
  show ((J cexBasis (cexData N).hom 1 x (fun _ _ _ => 1) : ℝ) : EReal) ≤ 0
  unfold J
  rw [hst]
  have h0 : costAlong cexBasis (cexData N).hom 1 (fun _ _ _ => 1) 0 = 0 := by
    simp [costAlong, Data.hom, cexData, Measure.restrict_singleton]
  rw [h0]
  simp

end SLQCex9ca7

open SLQSolv.Finite in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {n m : ℕ} (Bs : SLQSolv.Finite.Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d) (h56 : IsNonnegJ0 Bs d 0)
    (Pε : ℝ → ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hPε : ∀ ε > 0, IsStronglyRegular (d.addR ε) (Pε ε))
    (M0 : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hM0 : IsLyapunovSol d 0 M0)
    (ΦA : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hΦ : IsFundSolA d ΦA),
    (IsFinite Bs d.hom ↔ ∃ β : ℝ, ∀ ε > 0, (Pε ε 0 - β • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) ∧
    (IsFinite Bs d.hom → ∃ P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ,
      (∀ t ≤ d.T, Tendsto (fun ε => Pε ε t) (𝓝[>] 0) (𝓝 (P t))) ∧
      (∀ t ≤ d.T, ∀ x, V0 Bs d t x = (((P t *ᵥ x) ⬝ᵥ x : ℝ) : EReal)) ∧
      (∀ᵐ s ∂(volume.restrict (Icc (0:ℝ) d.T)), (sigmaR d P s.toNNReal).PosSemidef) ∧
      (∀ t ≤ d.T, (P t - nMat d M0 ΦA P t).PosSemidef ∧ (M0 t - P t).PosSemidef)) ∧
    (IsFiniteAtTime Bs d.hom 0 → IsFinite Bs d.hom)) := by
  intro H
  obtain ⟨N, hNm, hN⟩ := SLQCex9ca7.exists_bad
  obtain ⟨-, h2c, -⟩ := H SLQCex9ca7.cexBasis (SLQCex9ca7.cexData N) (SLQCex9ca7.h1_cex N hN)
    (SLQCex9ca7.h2_cex N) (SLQCex9ca7.h56_cex N) (fun _ _ => 1) (SLQCex9ca7.hPe_cex N hN)
    (fun _ => 1) (SLQCex9ca7.hM0_cex N) (fun _ => 1) (SLQCex9ca7.hPhi_cex N)
  obtain ⟨P, hlim, hV, -, -⟩ := h2c (SLQCex9ca7.isFinite_cex N)
  have hP1 : P 1 = 1 := tendsto_nhds_unique (hlim 1 le_rfl) tendsto_const_nhds
  have hv := hV 1 le_rfl (fun _ => 1)
  have hle := SLQCex9ca7.V0_le_zero N hNm hN (fun _ => 1)
  rw [hv, hP1] at hle
  simp [dotProduct] at hle
  exact absurd hle (not_le.mpr zero_lt_one)
