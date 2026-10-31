-- Prove2me | solution 1 for StochKolmogorov.Persist.markov_property
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T23:03:11.882169+00:00
-- url     : https://prove2.me/submissions/2bcfb3ab-0eb3-4e7f-b21c-f21d0f9e6494

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Persist_Model
import Theorems.Thm_EthierKurtz_sde_markov_property_lipschitz
import Theorems.Thm_StochKolmogorov_Persist_orthant_invariance_closed
import Theorems.Thm_StochKolmogorov_Persist_coord_ne_zero_of_pos

-- ===== ItoM1 =====

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ItoLib
open EthierKurtz

variable {Ω : Type*} {d : ℕ}

section BM
variable [MeasurableSpace Ω]

end BM

section AEC
variable {mΩ : MeasurableSpace Ω}

end AEC

section CP
variable [MeasurableSpace Ω]

end CP

section M2

variable [MeasurableSpace Ω]

end M2

section M3
variable [MeasurableSpace Ω]

end M3

section M4
variable [MeasurableSpace Ω]

end M4

section StopCoef

end StopCoef

section M5
variable [MeasurableSpace Ω]

end M5

section M5b

end M5b

section M5c
variable [MeasurableSpace Ω]

end M5c

section M6refine

end M6refine

section M6osc

end M6osc

section M6cauchy
variable [MeasurableSpace Ω]

end M6cauchy

section M6limit
variable [MeasurableSpace Ω]

end M6limit

section M6trunc

end M6trunc

section M6exist
variable [MeasurableSpace Ω]

end M6exist

section M7grid

end M7grid

section M7zero
variable [MeasurableSpace Ω]

end M7zero

section M7qv
variable [MeasurableSpace Ω]

end M7qv

section M7c
variable [MeasurableSpace Ω]

end M7c

section M8a
variable [MeasurableSpace Ω]

end M8a

section M8b
variable [MeasurableSpace Ω]

end M8b

section M8c
variable [MeasurableSpace Ω]

end M8c

section M8d
variable [MeasurableSpace Ω]

end M8d

section M8e
variable [MeasurableSpace Ω]

end M8e

section M8f
variable [MeasurableSpace Ω]

end M8f

section M8f2
variable [MeasurableSpace Ω]

end M8f2

section M8f3
variable [MeasurableSpace Ω]

end M8f3

section M8gTaylor
open Set

end M8gTaylor

section M8g
variable [MeasurableSpace Ω]

end M8g

section M8g2

end M8g2

section M8g3
variable [MeasurableSpace Ω]

end M8g3

section M8g4
variable [MeasurableSpace Ω]

end M8g4

section M8g5
variable [MeasurableSpace Ω]

end M8g5

section M9a
variable [MeasurableSpace Ω]

end M9a

section M9c
/-! M9c: calculus for the pathwise-uniqueness test function (line derivatives, cutoff). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

end M9cF

section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

end M9c2

section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

end M9d

section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

end M9d2

section M9e1
/-! Zero integral, measurability of time integrals, the exponential primitive identity, and the
pointwise generator bound with the localizing rate `kap`. -/

end M9e1

section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2

end ItoLib

-- ===== E =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10b1
/-! M10b-1: pathwise identification of Ito integrals. For an integrand that is an indefinite
integral in time (`h s = h 0 + ∫₀ˢ D`), left-point sums converge pathwise to the integration by
parts value `h t w t - h 0 w 0 - ∫₀ᵗ w D`; and pathwise limits of left-point sums are Ito
integrals in the sense of `HasBrownianItoIntegral`. -/

end M10b1

section M10b2
/-! M10b-2 (generic part): piecewise-linear interpolation of a sequence on the grid `k h`,
defined as a primitive of the piecewise-constant slope. -/

end M10b2

section M10b2s
/-! M10b-2: the truncated Euler scheme with lagged, linearly interpolated coefficients, driven by a
deterministic path `w`. `eulerZZ k = (Z_{k-1}, Z_k)`. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)
  (w : ℝ≥0 → SDEState d)

variable {s₁ b₁ h w}

end M10b2s

section M10b2w
/-! M10b-2 (random part): the scheme driven by a Brownian path is adapted, continuous, and an
Ito process. Measurability is proved for any monotone family `G` of σ-algebras that sees the
past of `W` (used with `G = completedBrownianPast` and with the ambient σ-algebra). -/

variable {W : ℝ≥0 → Ω → SDEState d} {G : ℝ≥0 → MeasurableSpace Ω}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10b2w

section M10b2i
/-! M10b-2: the scheme driven by standard Brownian motion is an Ito process in the sense of
`ito_formula`. -/

variable [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10b2i

section M10b4a
/-! M10b-4 (a): Ito formula for `Ff r` along `(X, Y, A)` where `X`, `Y` are general Ito
processes (matrix integrands `HX`, `HY`, drifts `bX`, `bY`), `A = ∫ κ(X, Y)`. -/

end M10b4a

section M10b4b
/-! M10b-4 (b): pathwise bounds for the generator `driftG` when `X` has coefficients
`σ₀(X), b₀(X)` and `Y` has arbitrary coefficients `σy, by'`. -/

end M10b4b

end ItoLib

-- ===== F =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c1
/-! M10c-1: the saturating profile `ψ(Q) = 1 - (1 - st(Q/4)) e^{-Q}` (`ψ(0) = 0`, `ψ = 1` for
`Q ≥ 4`, `ψ(Q) ≥ Q/5` on `[0,4]`) and the test function
`Gf r (x, y, a) = e^{-a} χ_r(|x|²) ψ(|x-y|²)` (cut-off in `x` only). -/

end M10c1

section M10c2
/-! M10c-2: the generator of `Gf r` along `(X, Y, A)` and its form inside the `x`-ball. -/

end M10c2

section M10c3
/-! M10c-3: pointwise bounds for the generator `driftH` of `Gf r`. -/

end M10c3

end ItoLib

-- ===== G =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c4
/-! M10c-4: the Ito formula along `(X, Y, A)` for an arbitrary `C²` test function `F` whose
martingale integrands are bounded (`ito_coupled_F`); applied to `Gf r`. -/

end M10c4

section M10c5
/-! M10c-5: expectation bound for `Gf r` along `(X, Y, A)`, `X` the SDE solution, `Y` a general
Ito process with globally bounded coefficients, clock rate `kapX` (penalising only `X`). -/

end M10c5

section M10c5s
/-! s33 STAB: stability in probability of an SDE solution against Ito processes whose
coefficients are close (in mean integrated square, inside `B̄_{R+3}`) to the SDE coefficients. -/

end M10c5s

section M10c6
/-! M10c-6: pathwise error of the truncated Euler scheme: on `[0, T]` the coefficient errors
`s₁(Y_u) - H_u`, `b₁(Y_u) - b_u` are `O(osc_w(h) + h)` (lag start `a = y`). -/

theorem euc_norm_le_sum' {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ k, |v k| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ k, ‖v k‖ ^ 2) ≤ √((∑ k, |v k|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ = ∑ k, |v k| := Real.sqrt_sq (Finset.sum_nonneg fun k _ => abs_nonneg _)

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c6

end ItoLib

-- ===== H =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c7
/-! M10c-7: the Euler scheme's coefficient error `‖s₁(Y_u) - H_u‖`, `‖b₁(Y_u) - b_u‖` is
`≤ 2 L K` with `K = d (3 d S δ + 2 S h)` (`δ` = oscillation of `w` over gaps `≤ h` on `[0, T]`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c7

section M10c8
/-! M10c-8: the coupled expectation bound `lintegral_Gf_le` with `Y` the truncated Euler scheme
driven by `W` (lag start `a = y = x₀`), `s₁ = σ₀`, `b₁ = b₀` on `B̄_{R+3}`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10c8

section M10c9
/-! M10c-9: `E ∫₀ᵗ eulerErr → 0` along any mesh sequence `hₙ → 0` (globally Lipschitz,
bounded truncated coefficients). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c9

section M10c10
/-! M10c-10: the truncated Euler scheme converges to the SDE solution in probability on the
event that `X` stays in `B̄_R` (truncation radius `≥ R + 3`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c10

end ItoLib

-- ===== I =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d1
/-! M10d-1 (b5 groundwork): the cell noise `ζ_j = (1/h) ∫₀ʰ (W(s+h) - W(s+u)) du`: measurable for
the future-increment σ-algebra (so independent of the completed past), mean zero, `E ζ² ≤ h/2`. -/

end M10d1

section M10d2
/-! M10d-2: one cell of the L² stability estimate: for completed-past-measurable `D` (L²) and
bounded `A, B`, `E‖D + N‖² ≤ E‖D‖² + 2 d h E(‖A‖² + ‖B‖²)` with the cell noise
`N_i = Σⱼ (A_ij ξ_j + B_ij ζ_j)`. -/

end M10d2

end ItoLib

-- ===== J =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d3
/-! M10d-3 (b5): one full cell of the Euler scheme in cell-noise form, and L² of the grid values. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

theorem coord_abs_le_state (x : SDEState d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i; rwa [Real.norm_eq_abs] at this

end M10d3

end ItoLib

-- ===== K =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e1
/-! M10e-1 (b6 groundwork): the scheme as a deterministic recursion `zrec` driven by the cell
noises `(ξ_l, ζ_l)`; restart identity `Z_{m+k} = zrec_k(Z_{m-1}, Z_m; noises of cells m, m+1, ...)`;
the noises after cell `m` are measurable for the future-increment σ-algebra. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable {s₁ b₁ h}

end M10e1

section M10e2
/-! M10e-2 (b6): restart at a grid time. Independence of the past pair `(Z_{m-1}, Z_m)` and the
future noises gives `E f(Z_{m+k}) = E[ E' f(zrec_k(Z_{m-1}, Z_m; noises after m)) ]`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e2

end ItoLib

-- ===== L =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e3
/-! M10e-3 (b6): time homogeneity. The restarted Brownian motion is standard; the noises after
cell `m` are the noises of the restarted motion; any two standard Brownian motions have the same
finite-dimensional laws. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10e3

section M10e4
/-! M10e-4 (b6 DONE): restart in law at a grid time: `E f(Z_{m+k}) = E G(Z_{m-1}, Z_m)` with
`G(a, y) = E f(Z_k from (a, y))`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e4

end ItoLib

-- ===== M =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f1
/-! M10f-1 (b7 groundwork): the restart function `G_k(a, y) = E f(Z_k from (a, y))` is Lipschitz
in the initial pair for Lipschitz `f`, uniformly in the mesh (via `euler_stab_exp`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f1

end ItoLib

-- ===== N =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f2
/-! M10f-2 (b7): uniform smallness of Euler cell increments, and the exit probability
`P(path leaves B̄_R before T) → 0`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {w : ℝ≥0 → SDEState d}

variable [MeasurableSpace Ω]

end M10f2

section M10f3
/-! M10f-3 (b7): the Euler scheme approximates `X_T` in law, up to the exit probability. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10f3

section M10f4
/-! M10f-4 (b7): the real-analysis wrap-up of the Chapman-Kolmogorov limit
(reverse Fatou in `n`, dominated convergence in `R`). -/

variable [MeasurableSpace Ω]

end M10f4

section M10f5
/-! M10f-5 (b7): the restart function `eulerG`, its bound and uniform Lipschitz property, and the
approximation `eulerG(y, y) ≈ E f(X^y_t)` up to the exit probability. -/

variable [MeasurableSpace Ω]

variable {P : Measure Ω} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f5

section M10f6
/-! M10f-6 (b7 DONE): Chapman-Kolmogorov in integrated form for bounded Lipschitz test functions,
with a measurable version `g` of `y ↦ E f(X^y_t)`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

theorem markov_core [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀)
    (s₁ : ℕ → SDEState d → SDEDiffusion d) (b₁ : ℕ → SDEState d → SDEState d) (S L : ℕ → ℝ)
    (hs₁ : ∀ R, Continuous (s₁ R)) (hb₁ : ∀ R, Continuous (b₁ R)) (hL : ∀ R, 0 ≤ L R)
    (hSg : ∀ R x, ‖s₁ R x‖ ≤ S R ∧ ‖b₁ R x‖ ≤ S R)
    (hLg : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L R * ‖x - y‖)
    (hag : ∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = σ₀ x ∧ b₁ R x = b₀ x)
    {D : Set (SDEState d)} {X : SDEState d → ℝ≥0 → Ω → SDEState d}
    (hX : ∀ y ∈ D, SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) (X y))
    (t : ℝ≥0) {f : SDEState d → ℝ} (hf : Measurable f) {K Lf : ℝ} (hfK : ∀ x, |f x| ≤ K)
    (hLf : 0 ≤ Lf) (hfL : ∀ x x', |f x - f x'| ≤ Lf * ‖x - x'‖) :
    ∃ g : SDEState d → ℝ, Measurable g ∧ (∀ y, |g y| ≤ K) ∧
      (∀ y ∈ D, g y = ∫ ω, f (X y t ω) ∂P) ∧
      ∀ x ∈ D, ∀ s : ℝ≥0, (∀ᵐ ω ∂P, X x s ω ∈ D) →
        ∫ ω, f (X x (s + t) ω) ∂P = ∫ ω, g (X x s ω) ∂P := by
  exact EthierKurtz.sde_markov_property_lipschitz hW hσ hb s₁ b₁ S L hs₁ hb₁ hL hSg hLg hag hX t hf hfK hLf hfL
end M10f6

end ItoLib

-- ===== O =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10g
/-! M10g: from integrated Chapman-Kolmogorov identities for thickened indicators (bounded
Lipschitz test functions) to a Markov kernel and set-wise Chapman-Kolmogorov. -/

theorem thick_props {δ : ℝ} (hδ : 0 < δ) (F : Set (SDEState d)) :
    Measurable (fun y => (thickenedIndicator hδ F y : ℝ)) ∧
      (∀ y, |(thickenedIndicator hδ F y : ℝ)| ≤ 1) ∧
      ∀ y y', |(thickenedIndicator hδ F y : ℝ) - thickenedIndicator hδ F y'| ≤ δ⁻¹ * ‖y - y'‖ := by
  refine ⟨(NNReal.continuous_coe.comp (thickenedIndicator hδ F).continuous).measurable,
    fun y => ?_, fun y y' => ?_⟩
  · rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast thickenedIndicator_le_one hδ F y
  · have := (lipschitzWith_thickenedIndicator hδ F).dist_le_mul y y'
    rw [NNReal.dist_eq, dist_eq_norm] at this
    simpa [Real.coe_toNNReal _ hδ.le] using this

variable [MeasurableSpace Ω] {P : Measure Ω}

theorem lint_thick [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) (F : Set (SDEState d))
    {V : Ω → SDEState d} (hV : Measurable V) :
    ∫⁻ y, (thickenedIndicator hδ F y : ℝ≥0∞) ∂(P.map V) =
      ENNReal.ofReal (∫ ω, (thickenedIndicator hδ F (V ω) : ℝ) ∂P) := by
  obtain ⟨hm, hb, -⟩ := thick_props hδ F
  have hmE : Measurable fun y => (thickenedIndicator hδ F y : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp (thickenedIndicator hδ F).continuous).measurable
  rw [lintegral_map hmE hV,
    ofReal_integral_eq_lintegral_ofReal (f := fun ω => (thickenedIndicator hδ F (V ω) : ℝ))
      (memLp_one_iff_integrable.1 (MemLp.of_bound (hm.comp hV).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb _)))
      (ae_of_all _ fun ω => NNReal.coe_nonneg _)]
  simp

theorem markov_of_core [IsProbabilityMeasure P] {D : Set (SDEState d)} (hDm : MeasurableSet D)
    {X : SDEState d → ℝ≥0 → Ω → SDEState d} (hXm : ∀ y ∈ D, ∀ t, Measurable (X y t)) (t : ℝ≥0)
    (Hc : ∀ (F : Set (SDEState d)), IsClosed F → ∀ n : ℕ, ∃ g : SDEState d → ℝ, Measurable g ∧
      (∀ y ∈ D, g y = ∫ ω, (thickenedIndicator (Nat.one_div_pos_of_nat (n := n)) F (X y t ω) : ℝ) ∂P) ∧
      ∀ x ∈ D, ∀ s : ℝ≥0, (∀ᵐ ω ∂P, X x s ω ∈ D) →
        ∫ ω, (thickenedIndicator (Nat.one_div_pos_of_nat (n := n)) F (X x (s + t) ω) : ℝ) ∂P =
          ∫ ω, g (X x s ω) ∂P) :
    ∃ κ : Kernel (SDEState d) (SDEState d), IsMarkovKernel κ ∧ (∀ x ∈ D, κ x = P.map (X x t)) ∧
      ∀ x ∈ D, ∀ s : ℝ≥0, (∀ᵐ ω ∂P, X x s ω ∈ D) → ∀ A, MeasurableSet A →
        P.map (X x (s + t)) A = ∫⁻ y, P.map (X y t) A ∂(P.map (X x s)) := by
  classical
  choose g hgm hgD hgck using Hc
  set κ0 : SDEState d → Measure (SDEState d) :=
    fun x => if x ∈ D then P.map (X x t) else Measure.dirac x with hκ0
  have hprob : ∀ x, IsProbabilityMeasure (κ0 x) := fun x => by
    by_cases hx : x ∈ D
    · simp only [hκ0, if_pos hx]; exact Measure.isProbabilityMeasure_map (hXm x hx t).aemeasurable
    · simp only [hκ0, if_neg hx]; infer_instance
  have hδ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : ∀ F (hF : IsClosed F), ∀ x ∈ D,
      Tendsto (fun n => ENNReal.ofReal (g F hF n x)) atTop (𝓝 (κ0 x F)) := by
    intro F hF x hx
    have := tendsto_lintegral_thickenedIndicator_of_isClosed (P.map (X x t)) hF
      (fun n => Nat.one_div_pos_of_nat) hδ
    simp only [hκ0, if_pos hx]
    refine this.congr fun n => ?_
    rw [lint_thick _ _ (hXm x hx t), hgD F hF n x hx]
  have hmeasF : ∀ F, IsClosed F → Measurable fun x => κ0 x F := by
    intro F hF
    refine measurable_of_tendsto_metrizable (f := fun n => D.piecewise
      (fun x => ENNReal.ofReal (g F hF n x)) (fun x => Measure.dirac x F)) (fun n => ?_) ?_
    · refine Measurable.piecewise hDm (ENNReal.measurable_ofReal.comp (hgm F hF n)) ?_
      have : (fun x => Measure.dirac x F) = F.indicator 1 := funext fun x =>
        Measure.dirac_apply' x hF.measurableSet
      rw [this]; exact measurable_one.indicator hF.measurableSet
    · rw [tendsto_pi_nhds]
      intro x
      by_cases hx : x ∈ D
      · have e : ∀ n : ℕ, D.piecewise (fun x => ENNReal.ofReal (g F hF n x))
            (fun x => Measure.dirac x F) x = ENNReal.ofReal (g F hF n x) := fun n =>
          Set.piecewise_eq_of_mem _ _ _ hx
        simp only [e]; exact hlim F hF x hx
      · have e : ∀ n : ℕ, D.piecewise (fun x => ENNReal.ofReal (g F hF n x))
            (fun x => Measure.dirac x F) x = Measure.dirac x F := fun n =>
          Set.piecewise_eq_of_notMem _ _ _ hx
        simp only [e, hκ0, if_neg hx]; exact tendsto_const_nhds
  have hgen : (inferInstance : MeasurableSpace (SDEState d)) =
      MeasurableSpace.generateFrom {s | IsClosed s} :=
    (BorelSpace.measurable_eq (α := SDEState d)).trans borel_eq_generateFrom_isClosed
  haveI := hprob
  have hκm : Measurable κ0 := Measurable.measure_of_isPiSystem_of_isProbabilityMeasure hgen
    isPiSystem_isClosed fun F hF => hmeasF F hF
  refine ⟨⟨κ0, hκm⟩, ⟨fun x => hprob x⟩, fun x hx => by
    show κ0 x = _; simp only [hκ0, if_pos hx], ?_⟩
  intro x hx s hD A hA
  have hXs := hXm x hx s
  have hDmap : ∀ᵐ y ∂(P.map (X x s)), y ∈ D := (ae_map_iff hXs.aemeasurable hDm).2 hD
  haveI : IsProbabilityMeasure (P.map (X x (s + t))) :=
    Measure.isProbabilityMeasure_map (hXm x hx (s + t)).aemeasurable
  haveI : IsProbabilityMeasure (P.map (X x s)) := Measure.isProbabilityMeasure_map hXs.aemeasurable
  have hbind_univ : (P.map (X x s)).bind κ0 Set.univ = 1 := by
    rw [Measure.bind_apply MeasurableSet.univ hκm.aemeasurable]
    simp [fun y => (hprob y).measure_univ]
  have hbind : P.map (X x (s + t)) = (P.map (X x s)).bind κ0 := by
    refine ext_of_generate_finite _ hgen isPiSystem_isClosed (fun F hF => ?_) (by
      rw [hbind_univ, measure_univ])
    haveI : IsFiniteMeasure ((P.map (X x s)).bind κ0) := ⟨by rw [hbind_univ]; exact ENNReal.one_lt_top⟩
    have h1 := tendsto_lintegral_thickenedIndicator_of_isClosed (P.map (X x (s + t))) hF
      (fun n => Nat.one_div_pos_of_nat) hδ
    have h2 := tendsto_lintegral_thickenedIndicator_of_isClosed ((P.map (X x s)).bind κ0) hF
      (fun n => Nat.one_div_pos_of_nat) hδ
    refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
    obtain ⟨hm, hb, -⟩ := thick_props (Nat.one_div_pos_of_nat (n := n) (α := ℝ)) F
    have hgnn : ∀ y ∈ D, 0 ≤ g F hF n y := fun y hy => by
      rw [hgD F hF n y hy]; exact integral_nonneg fun ω => NNReal.coe_nonneg _
    have hgb : ∀ y ∈ D, |g F hF n y| ≤ 1 := fun y hy => by
      rw [hgD F hF n y hy, abs_of_nonneg (integral_nonneg fun ω => NNReal.coe_nonneg _)]
      refine (integral_mono_of_nonneg (ae_of_all _ fun ω => NNReal.coe_nonneg _)
        (integrable_const (1 : ℝ)) (ae_of_all _ fun ω => ?_)).trans (by simp)
      exact (le_abs_self _).trans (hb _)
    have hmE : Measurable fun y => (thickenedIndicator (Nat.one_div_pos_of_nat (n := n) (α := ℝ)) F y : ℝ≥0∞) :=
      (ENNReal.continuous_coe.comp (thickenedIndicator _ F).continuous).measurable
    rw [Measure.lintegral_bind hκm.aemeasurable hmE.aemeasurable,
      lint_thick _ _ (hXm x hx (s + t)), hgck F hF n x hx s hD,
      lintegral_map' ?_ hXs.aemeasurable]
    · rw [ofReal_integral_eq_lintegral_ofReal]
      · refine lintegral_congr_ae (hD.mono fun ω hω => ?_)
        simp only [hκ0, if_pos hω]
        rw [lint_thick _ _ (hXm _ hω t), hgD F hF n _ hω]
      · exact memLp_one_iff_integrable.1 (MemLp.of_bound ((hgm F hF n).comp hXs).aestronglyMeasurable 1
          (hD.mono fun ω hω => by rw [Real.norm_eq_abs]; exact hgb _ hω))
      · exact hD.mono fun ω hω => hgnn _ hω
    · exact ((Measure.measurable_lintegral hmE).comp hκm).aemeasurable
  rw [hbind, Measure.bind_apply hA hκm.aemeasurable]
  refine lintegral_congr_ae (hDmap.mono fun y hy => ?_)
  simp only [hκ0, if_pos hy]

end M10g

end ItoLib

-- ===== P =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10h
/-! M10h (b9/b11): local Lipschitz on compact sets, coordinate clamps, truncation families,
and the Kolmogorov coefficients. -/

/-- Local Lipschitz on `s` gives a Lipschitz bound on every compact `K ⊆ s`. -/
theorem lipOn_of_locLip_compact {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {s K : Set α} {f : α → β} (hf : LocallyLipschitzOn s f) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ y ∈ K, dist (f x) (f y) ≤ L * dist x y := by
  classical
  have hloc : ∀ x : K, ∃ r > (0 : ℝ), ∃ L : ℝ≥0, LipschitzOnWith L f (Metric.ball (x : α) r ∩ s) := by
    intro x
    obtain ⟨L, t, ht, hL⟩ := hf (hKs x.2)
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhdsWithin_iff.1 ht
    exact ⟨r, hr, L, hL.mono hrt⟩
  choose r hr L hL using hloc
  have hcov : K ⊆ ⋃ x : K, Metric.ball (x : α) (r x / 2) := fun y hy =>
    Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (half_pos (hr _))⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover _ (fun _ => Metric.isOpen_ball) hcov
  -- bound on `f` over `K`
  have hbdd : Bornology.IsBounded (f '' K) :=
    (hK.image_of_continuousOn (hf.continuousOn.mono hKs)).isBounded
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hbdd
  by_cases hTn : T.Nonempty
  · set δ : ℝ := T.inf' hTn (fun x => r x / 2) with hδ
    have hδpos : 0 < δ := by
      rw [hδ, Finset.lt_inf'_iff]; exact fun x _ => half_pos (hr x)
    set Lm : ℝ≥0 := T.sup L
    refine ⟨Lm + max C 0 / δ, by positivity, fun x hx y hy => ?_⟩
    by_cases hxy : dist x y < δ
    · obtain ⟨z, hzT, hxz⟩ : ∃ z ∈ T, x ∈ Metric.ball (z : α) (r z / 2) := by
        have := hT hx; simp only [Set.mem_iUnion] at this
        obtain ⟨z, hz, h⟩ := this; exact ⟨z, hz, h⟩
      have hδz : δ ≤ r z / 2 := Finset.inf'_le _ hzT
      have hx' : x ∈ Metric.ball (z : α) (r z) ∩ s :=
        ⟨Metric.ball_subset_ball (by linarith [hr z]) hxz, hKs hx⟩
      have hy' : y ∈ Metric.ball (z : α) (r z) ∩ s := by
        refine ⟨?_, hKs hy⟩
        rw [Metric.mem_ball] at hxz ⊢
        calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
          _ < δ + r z / 2 := by rw [dist_comm]; exact add_lt_add hxy hxz
          _ ≤ r z := by linarith
      have h1 := (hL z).dist_le_mul x hx' y hy'
      have h2 : (L z : ℝ) ≤ Lm := by exact_mod_cast Finset.le_sup (f := L) hzT
      have h3 : 0 ≤ max C 0 / δ * dist x y := by positivity
      nlinarith [dist_nonneg (x := x) (y := y)]
    · replace hxy := not_lt.1 hxy
      have h1 : dist (f x) (f y) ≤ max C 0 :=
        (hC ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩).trans (le_max_left _ _)
      have h2 : max C 0 ≤ max C 0 / δ * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
        exact mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
      have h3 : 0 ≤ (Lm : ℝ) * dist x y := by positivity
      nlinarith
  · have hK0 : K = ∅ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hTn
      subst hTn; simpa using hT
    exact ⟨0, le_rfl, fun x hx => by simp [hK0] at hx⟩

variable {d : ℕ}

/-- Coordinatewise 1-Lipschitz maps are 1-Lipschitz in the Euclidean norm. -/
theorem norm_sub_le_of_coord {x y x' y' : SDEState d} (h : ∀ i, |x' i - y' i| ≤ |x i - y i|) :
    ‖x' - y'‖ ≤ ‖x - y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.sub_apply, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

theorem clamp1_lip (M a b : ℝ) : |max (-M) (min M a) - max (-M) (min M b)| ≤ |a - b| := by
  rw [abs_le]
  have h1 := le_abs_self (a - b); have h2 := neg_abs_le (a - b)
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- Coordinate clamp to the box `[-M, M]^d`. -/
noncomputable def clampM (M : ℝ) (x : SDEState d) : SDEState d :=
  WithLp.toLp 2 (fun i => max (-M) (min M (x i)))

theorem clampM_apply (M : ℝ) (x : SDEState d) (i : Fin d) :
    clampM M x i = max (-M) (min M (x i)) := rfl

theorem clampM_lip (M : ℝ) (x y : SDEState d) : ‖clampM M x - clampM M y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by rw [clampM_apply, clampM_apply]; exact clamp1_lip _ _ _

theorem clampM_abs_le {M : ℝ} (hM : 0 ≤ M) (x : SDEState d) (i : Fin d) : |clampM M x i| ≤ M := by
  rw [clampM_apply, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clampM_eq {M : ℝ} {x : SDEState d} (hx : ‖x‖ ≤ M) : clampM M x = x := by
  ext i
  rw [clampM_apply]
  have := (coord_abs_le_state x i).trans hx
  rw [abs_le] at this
  rw [min_eq_right this.2, max_eq_right this.1]

theorem norm_le_card_mul {M : ℝ} {x : SDEState d} (hx : ∀ i, |x i| ≤ M) : ‖x‖ ≤ d * M := by
  calc ‖x‖ ≤ ∑ i, |x i| := euc_norm_le_sum' x
    _ ≤ ∑ _i : Fin d, M := Finset.sum_le_sum fun i _ => hx i
    _ = d * M := by simp

/-- b9: a truncation family for coordinate functions that are Lipschitz on every box. -/
theorem trunc_family {ι : Type*} [Fintype ι] (φ : ι → SDEState d → ℝ)
    (hL : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ k x y, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |φ k x - φ k y| ≤ L * ‖x - y‖) :
    ∃ (s₁ : ℕ → SDEState d → EuclideanSpace ℝ ι) (S L : ℕ → ℝ), (∀ R, Continuous (s₁ R)) ∧
      (∀ R, 0 ≤ L R) ∧ (∀ R x, ‖s₁ R x‖ ≤ S R) ∧
      (∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖) ∧
      (∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = WithLp.toLp 2 (fun k => φ k x)) := by
  classical
  choose Lb hLb0 hLb using fun R : ℕ => hL ((R : ℝ) + 3) (by positivity)
  set s₁ : ℕ → SDEState d → EuclideanSpace ℝ ι :=
    fun R x => WithLp.toLp 2 (fun k => φ k (clampM ((R : ℝ) + 3) x)) with hs₁
  have hM : ∀ R : ℕ, (0 : ℝ) ≤ (R : ℝ) + 3 := fun R => by positivity
  have hlip : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ (Fintype.card ι * Lb R) * ‖x - y‖ := by
    intro R x y
    calc ‖s₁ R x - s₁ R y‖ ≤ ∑ k, |(s₁ R x - s₁ R y) k| := euc_norm_le_sum' _
      _ ≤ ∑ _k : ι, Lb R * ‖x - y‖ := by
          apply Finset.sum_le_sum; intro k _
          simp only [hs₁, PiLp.sub_apply]
          exact (hLb R k _ _ (clampM_abs_le (hM R) x) (clampM_abs_le (hM R) y)).trans
            (mul_le_mul_of_nonneg_left (clampM_lip _ _ _) (hLb0 R))
      _ = (Fintype.card ι * Lb R) * ‖x - y‖ := by simp [mul_assoc]
  refine ⟨s₁, fun R => ∑ k : ι, (|φ k (clampM ((R : ℝ) + 3) 0)| + Lb R * (2 * (d * ((R : ℝ) + 3)))),
    fun R => Fintype.card ι * Lb R, fun R => ?_, fun R => by have := hLb0 R; positivity,
    fun R x => ?_, hlip, fun R x hx => ?_⟩
  · exact LipschitzWith.continuous (K := ⟨Fintype.card ι * Lb R, by have := hLb0 R; positivity⟩)
      (LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]; exact hlip R x y)
  · calc ‖s₁ R x‖ ≤ ∑ k, |s₁ R x k| := euc_norm_le_sum' _
      _ ≤ _ := by
          apply Finset.sum_le_sum; intro k _
          simp only [hs₁]
          set M : ℝ := (R : ℝ) + 3
          have hc := hLb R k _ _ (clampM_abs_le (hM R) x) (clampM_abs_le (hM R) 0)
          have hn : ‖clampM M x - clampM M 0‖ ≤ 2 * (d * M) := by
            calc ‖clampM M x - clampM M 0‖ ≤ ‖clampM M x‖ + ‖clampM M 0‖ := norm_sub_le _ _
              _ ≤ d * M + d * M := add_le_add (norm_le_card_mul (clampM_abs_le (hM R) x))
                  (norm_le_card_mul (clampM_abs_le (hM R) 0))
              _ = 2 * (d * M) := by ring
          have := mul_le_mul_of_nonneg_left hn (hLb0 R)
          have h3 := abs_sub_abs_le_abs_sub (φ k (clampM M x)) (φ k (clampM M 0))
          linarith
  · simp only [hs₁, clampM_eq hx]

end M10h

section M10i
open StochKolmogorov.Persist
variable {n : ℕ}

theorem posPart_apply' (x : SDEState n) (i : Fin n) : posPart x i = max (x i) 0 := rfl

theorem posPart_lip (x y : SDEState n) : ‖posPart x - posPart y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by
    rw [posPart_apply', posPart_apply']; exact abs_max_sub_max_le_abs _ _ _

theorem posPart_mem_orthant (x : SDEState n) : posPart x ∈ orthant n := fun i => by
  rw [posPart_apply']; exact le_max_right _ _

theorem continuous_posPart : Continuous (posPart (n := n)) :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]; exact posPart_lip x y)

/-- A locally Lipschitz function on the orthant, read at `x⁺`, is Lipschitz and bounded on boxes. -/
theorem locLip_posPart_box {h : SDEState n → ℝ} (hh : LocallyLipschitzOn (orthant n) h)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ L G : ℝ, 0 ≤ L ∧ 0 ≤ G ∧ ∀ x y : SDEState n, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |h (posPart x) - h (posPart y)| ≤ L * ‖x - y‖ ∧ |h (posPart x)| ≤ G := by
  set K : Set (SDEState n) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ M} with hKdef
  have hKc : IsClosed K := by
    have : K = ⋂ i, ({y : SDEState n | 0 ≤ y i} ∩ {y | y i ≤ M}) := by
      ext y; simp [hKdef, forall_and]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).inter
      (isClosed_le (PiLp.continuous_apply 2 _ i) continuous_const)
  have hKb : Bornology.IsBounded K := (Metric.isBounded_closedBall (x := (0 : SDEState n))
      (r := n * M)).subset fun y hy => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_card_mul fun i => by rw [abs_of_nonneg (hy i).1]; exact (hy i).2
  have hKo : K ⊆ orthant n := fun y hy i => (hy i).1
  obtain ⟨L, hL0, hL⟩ := lipOn_of_locLip_compact hh (Metric.isCompact_of_isClosed_isBounded hKc hKb) hKo
  have hpK : ∀ x : SDEState n, (∀ i, |x i| ≤ M) → posPart x ∈ K := fun x hx i => by
    rw [posPart_apply']
    exact ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hx i)) hM⟩
  have h0 : ∀ i, |(0 : SDEState n) i| ≤ M := fun i => by simpa using hM
  refine ⟨L, L * (n * M) + |h (posPart 0)|, hL0, by positivity, fun x y hx hy => ⟨?_, ?_⟩⟩
  · have := hL _ (hpK x hx) _ (hpK y hy)
    rw [Real.dist_eq, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (posPart_lip x y) hL0)
  · have h1 := hL _ (hpK x hx) _ (hpK 0 h0)
    rw [Real.dist_eq, dist_eq_norm] at h1
    have h2 : ‖posPart x - posPart (0 : SDEState n)‖ ≤ n * M := by
      calc ‖posPart x - posPart (0 : SDEState n)‖ ≤ ‖x - 0‖ := posPart_lip x 0
        _ = ‖x‖ := by rw [sub_zero]
        _ ≤ n * M := norm_le_card_mul hx
    have h3 := abs_sub_abs_le_abs_sub (h (posPart x)) (h (posPart 0))
    have h4 := mul_le_mul_of_nonneg_left h2 hL0
    linarith

/-- Products `x_i · h(x⁺) · c` are Lipschitz on boxes. -/
theorem prod_box_lip {h : SDEState n → ℝ} (hh : LocallyLipschitzOn (orthant n) h) (c : ℝ) (i : Fin n)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : SDEState n, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x i * h (posPart x) * c - y i * h (posPart y) * c| ≤ L * ‖x - y‖ := by
  obtain ⟨L, G, hL0, hG0, hLG⟩ := locLip_posPart_box hh hM
  refine ⟨|c| * (M * L + G), by positivity, fun x y hx hy => ?_⟩
  obtain ⟨h1, -⟩ := hLG x y hx hy
  obtain ⟨-, h2⟩ := hLG y x hy hx
  have hxy : |x i - y i| ≤ ‖x - y‖ := by
    have := coord_abs_le_state (x - y) i; rwa [PiLp.sub_apply] at this
  have e : x i * h (posPart x) * c - y i * h (posPart y) * c =
      c * (x i * (h (posPart x) - h (posPart y)) + h (posPart y) * (x i - y i)) := by ring
  rw [e, abs_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  calc |x i * (h (posPart x) - h (posPart y)) + h (posPart y) * (x i - y i)|
      ≤ |x i| * |h (posPart x) - h (posPart y)| + |h (posPart y)| * |x i - y i| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ M * (L * ‖x - y‖) + G * ‖x - y‖ := by
        gcongr
        · exact hx i
    _ = (M * L + G) * ‖x - y‖ := by ring

/-- b11: the Kolmogorov coefficients are continuous and have truncation families as needed by
`markov_core`. -/
theorem kolm_trunc (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Continuous (fun x : SDEState n => diffusion C (0, x)) ∧
    Continuous (fun x : SDEState n => drift C (0, x)) ∧
    ∃ (s₁ : ℕ → SDEState n → SDEDiffusion n) (b₁ : ℕ → SDEState n → SDEState n) (S L : ℕ → ℝ),
      (∀ R, Continuous (s₁ R)) ∧ (∀ R, Continuous (b₁ R)) ∧ (∀ R, 0 ≤ L R) ∧
      (∀ R x, ‖s₁ R x‖ ≤ S R ∧ ‖b₁ R x‖ ≤ S R) ∧
      (∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L R * ‖x - y‖) ∧
      (∀ (R : ℕ) (x : SDEState n), ‖x‖ ≤ (R : ℝ) + 3 →
        s₁ R x = diffusion C (0, x) ∧ b₁ R x = drift C (0, x)) := by
  have hgc : ∀ i, Continuous fun x : SDEState n => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hfc : ∀ i, Continuous fun x : SDEState n => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  refine ⟨(PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      (((PiLp.continuous_apply 2 _ k.1).mul (hgc k.1)).mul continuous_const)),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      ((PiLp.continuous_apply 2 _ k).mul (hfc k))), ?_⟩
  -- the two coordinate families
  have hLs : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ (k : Fin n × Fin n) (x y : SDEState n),
      (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x k.1 * C.g k.1 (posPart x) * C.Γ k.2 k.1 - y k.1 * C.g k.1 (posPart y) * C.Γ k.2 k.1|
        ≤ L * ‖x - y‖ := by
    intro M hM
    choose L hL0 hL using fun k : Fin n × Fin n => prod_box_lip (hC k.1).2 (C.Γ k.2 k.1) k.1 hM
    refine ⟨∑ k, L k, Finset.sum_nonneg fun k _ => hL0 k, fun k x y hx hy => ?_⟩
    exact (hL k x y hx hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hL0 k) (Finset.mem_univ k)) (norm_nonneg _))
  have hLb : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ (k : Fin n) (x y : SDEState n),
      (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x k * C.f k (posPart x) * 1 - y k * C.f k (posPart y) * 1| ≤ L * ‖x - y‖ := by
    intro M hM
    choose L hL0 hL using fun k : Fin n => prod_box_lip (hC k).1 1 k hM
    refine ⟨∑ k, L k, Finset.sum_nonneg fun k _ => hL0 k, fun k x y hx hy => ?_⟩
    exact (hL k x y hx hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hL0 k) (Finset.mem_univ k)) (norm_nonneg _))
  obtain ⟨s₁, S1, L1, hs1c, hL1, hS1, hl1, he1⟩ := trunc_family _ hLs
  obtain ⟨b₁, S2, L2, hb1c, hL2, hS2, hl2, he2⟩ := trunc_family _ hLb
  refine ⟨s₁, b₁, fun R => max (S1 R) (S2 R), fun R => max (L1 R) (L2 R), hs1c, hb1c,
    fun R => (hL1 R).trans (le_max_left _ _), fun R x => ⟨(hS1 R x).trans (le_max_left _ _),
      (hS2 R x).trans (le_max_right _ _)⟩, fun R x y => ⟨(hl1 R x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)), (hl2 R x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩, fun R x hx => ⟨?_, ?_⟩⟩
  · rw [he1 R x hx]; rfl
  · rw [he2 R x hx]; simp only [mul_one]; rfl

end M10i

section M10j
open StochKolmogorov.Persist
variable {n : ℕ}

theorem orthant_isClosed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

end M10j

end ItoLib

-- ===== Q =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10k
/-! M10k (b10 calculus): the cubic negative part `φ(v) = (v⁻)³` (C², `v φ' = 3φ`, `v² φ'' = 6φ`)
and the orthant test function `Hf r u = e^{-a} χ_r(|x|²) Σ_k φ(x_k)`. -/

variable {d : ℕ}

end M10k

section M10l
/-! M10l (b10 drift): generator of `Hf r` inside the ball and its global bound. -/
variable {d : ℕ}

end M10l

section M10m
/-! M10m (b10 expectation): `E Hf_r(X_t) ≤ Hf_r(x₀) + B/M` along `(X, X, A)`. -/
variable {Ω : Type*} {d : ℕ}

end M10m

end ItoLib

-- ===== R =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10n
/-! M10n (b10 expectation and Markov step): `E Hf_r(X_t, A_t) ≤ Hf_r(x₀) + B/M`, and
`P{X stays in B̄_R on [0,t], ε < Φ(X_t)} ≤ (Hf_r(x₀) + B/M) / (e^{-ct} ε)`. -/
variable {Ω : Type*} {d : ℕ}

end M10n

end ItoLib

-- ===== S =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10o
/-! M10o (b10 done): orthant invariance of the Kolmogorov solutions, and the Markov statement. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M10o

end ItoLib

-- ===== V =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11c
/-! M11c: the orthant test-function machinery of Q.lean/R.lean with a general family of C²
nonnegative coordinate functions `φ k` in place of `(v⁻)³`. -/

variable {Ω : Type*} {d : ℕ}

variable {φ : Fin d → ℝ → ℝ} [hφ : Fact (∀ k, ContDiff ℝ 2 (φ k))]
  [hφ0 : Fact (∀ k v, 0 ≤ φ k v)]

end M11c

end ItoLib

-- ===== W =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11d
/-! M11d (lemma_3_1 clause 3, interior part): a solution started with `x_k > 0` has `X_t k ≠ 0`
almost surely at every fixed time. Test function `φ_δ(v) = 1/(v² + δ)`, with
`|φ_δ'(v) v| ≤ 2 φ_δ(v)` and `φ_δ''(v) v² ≤ 8 φ_δ(v)`. -/
open StochKolmogorov.Persist

variable {δ : ℝ}

variable {n : ℕ}

/-- `orthant_inv` for one solution (no solution family needed). -/
theorem orthant_inv1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (hx₀ : x₀ ∈ orthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω ∈ orthant n := by
  exact StochKolmogorov.Persist.orthant_invariance_closed P C B hB hC hx₀ hY t
/-- lemma_3_1 clause 3 (interior coordinates, fixed time): `x_k > 0` gives `X_t k ≠ 0` a.s. -/
theorem coord_ne_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (k : Fin n) (hk : 0 < x₀ k) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω k ≠ 0 := by
  exact StochKolmogorov.Persist.coord_ne_zero_of_pos P C B hB hC k hk hY t
/-- Solutions started in the open orthant are in the open orthant at each fixed time, a.s. -/
theorem openOrthant_inv1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (hx₀ : x₀ ∈ openOrthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω ∈ openOrthant n := by
  have h0 := orthant_inv1 P C B hB hC (fun i => (hx₀ i).le) hY t
  have h1 := ae_all_iff.2 fun k => coord_ne_zero P C B hB hC k (hx₀ k) hY t
  filter_upwards [h0, h1] with ω hω0 hω1
  exact fun i => lt_of_le_of_ne (hω0 i) (hω1 i).symm

theorem openOrthant_isOpen : IsOpen (openOrthant n) := by
  have : openOrthant n = ⋂ i, {x : SDEState n | 0 < x i} := by ext x; simp [openOrthant]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)

end M11d

end ItoLib

-- ===== TA =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section TA
/-! TA (s31): universe-polymorphic Markov statement (Ω : Type*), for the theorem_1_1 glue. -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- b12: the Markov statement, given orthant invariance of the solutions. -/
theorem markov_stmt_of_inv' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n) :
    (∀ t : ℝ≥0, ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
        ∀ x ∈ orthant n, κ x = trans P X t x) ∧
    ∀ (s t : ℝ≥0) (x : SDEState n), x ∈ orthant n → ∀ A : Set (SDEState n), MeasurableSet A →
      trans P X (s + t) x A = ∫⁻ y, trans P X t y A ∂(trans P X s x) := by
  obtain ⟨hP, hB, hX⟩ := hfam
  obtain ⟨hσc, hbc, s₁, b₁, S, L, hs₁, hb₁, hL, hSg, hLg, hag⟩ := kolm_trunc C hC
  have hXm : ∀ y ∈ orthant n, ∀ t, Measurable (X y t) := fun y hy t => (hX y hy).1 t
  have hX' : ∀ y ∈ orthant n, SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => y) (X y) := fun y hy => hX y hy
  have hcore : ∀ t : ℝ≥0, ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
      (∀ x ∈ orthant n, κ x = P.map (X x t)) ∧
      ∀ x ∈ orthant n, ∀ s : ℝ≥0, (∀ᵐ ω ∂P, X x s ω ∈ orthant n) → ∀ A, MeasurableSet A →
        P.map (X x (s + t)) A = ∫⁻ y, P.map (X y t) A ∂(P.map (X x s)) := by
    intro t
    refine markov_of_core orthant_isClosed.measurableSet hXm t fun F _ m => ?_
    obtain ⟨hm, hb, hl⟩ := thick_props (Nat.one_div_pos_of_nat (n := m)) F
    obtain ⟨g, hg, -, hg1, hg2⟩ := markov_core hB hσc hbc s₁ b₁ S L hs₁ hb₁ hL hSg hLg hag hX' t hm hb
      (inv_nonneg.2 (Nat.one_div_pos_of_nat (n := m)).le) hl
    exact ⟨g, hg, hg1, hg2⟩
  refine ⟨fun t => ?_, fun s t x hx A hA => ?_⟩
  · obtain ⟨κ, hκ, hκx, -⟩ := hcore t
    exact ⟨κ, hκ, hκx⟩
  · obtain ⟨κ, -, -, hck⟩ := hcore t
    exact hck x hx s (hinv x hx s) A hA

end TA

end ItoLib

-- ===== TC =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section TC
/-! TC (s31): the new child `StochKolmogorov.Persist.markov_property` of the theorem_1_1 reduction. -/
open StochKolmogorov.Persist
variable {n : ℕ}

theorem orthant_invariance_lib {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    (∀ x ∈ orthant n, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X x t ω ∈ orthant n) ∧
    (∀ x ∈ openOrthant n, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X x t ω ∈ openOrthant n) := by
  obtain ⟨hP, hB, hXs⟩ := hX
  exact ⟨fun x hx t => orthant_inv1 P C B hB hA.2.1 hx (hXs x hx) t,
    fun x hx t => openOrthant_inv1 P C B hB hA.2.1 hx (hXs x fun i => (hx i).le) t⟩

theorem markov_property_proof {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    (∀ t : ℝ≥0, ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
        ∀ x ∈ orthant n, κ x = trans P X t x) ∧
    (∀ (s t : ℝ≥0) (x : SDEState n), x ∈ orthant n → ∀ A : Set (SDEState n), MeasurableSet A →
        trans P X (s + t) x A = ∫⁻ y, trans P X t y A ∂(trans P X s x)) ∧
    (∀ (t : ℝ≥0) (x : SDEState n), x ∈ orthant n → trans P X t x (orthant n)ᶜ = 0) ∧
    (∀ (t : ℝ≥0) (x : SDEState n), x ∈ openOrthant n → trans P X t x (openOrthant n)ᶜ = 0) := by
  have hI := orthant_invariance_lib P C B X hX c γb hA
  obtain ⟨h1, h2⟩ := markov_stmt_of_inv' P C B X hX hA.2.1 hI.1
  refine ⟨h1, h2, fun t x hx => ?_, fun t x hx => ?_⟩
  · have hm : Measurable (X x t) := (hX.2.2 x hx).1 t
    unfold StochKolmogorov.Persist.trans
    rw [Measure.map_apply hm orthant_isClosed.measurableSet.compl]
    exact measure_mono_null (fun ω hω => hω) (ae_iff.1 (hI.1 x hx t))
  · have hm : Measurable (X x t) := (hX.2.2 x fun i => (hx i).le).1 t
    unfold StochKolmogorov.Persist.trans
    rw [Measure.map_apply hm openOrthant_isOpen.measurableSet.compl]
    exact measure_mono_null (fun ω hω => hω) (ae_iff.1 (hI.2 x hx t))

end TC

end ItoLib

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators in
open StochKolmogorov.Persist in
open EthierKurtz in
set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    (∀ t : ℝ≥0, ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
        ∀ x ∈ orthant n, κ x = trans P X t x) ∧
    (∀ (s t : ℝ≥0) (x : SDEState n), x ∈ orthant n → ∀ A : Set (SDEState n), MeasurableSet A →
        trans P X (s + t) x A = ∫⁻ y, trans P X t y A ∂(trans P X s x)) ∧
    (∀ (t : ℝ≥0) (x : SDEState n), x ∈ orthant n → trans P X t x (orthant n)ᶜ = 0) ∧
    (∀ (t : ℝ≥0) (x : SDEState n), x ∈ openOrthant n → trans P X t x (openOrthant n)ᶜ = 0) := by
  exact ItoLib.markov_property_proof P C B X hX c γb hA
