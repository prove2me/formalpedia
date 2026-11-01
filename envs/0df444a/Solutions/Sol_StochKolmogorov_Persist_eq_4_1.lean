-- Prove2me | solution 1 for StochKolmogorov.Persist.eq_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T21:11:19.117479+00:00
-- url     : https://prove2.me/submissions/9e9381cb-9253-4314-94e1-5db37e8553c7

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Definitions.Def_TotalVariationDist
import Theorems.Thm_StochKolmogorov_Persist_markov_property
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_sde_face_invariance
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_2
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_3
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_face_box_tv_overlap
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

variable [MeasurableSpace Ω] {P : Measure Ω}

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

variable {d : ℕ}

end M10h

section M10i
open StochKolmogorov.Persist
variable {n : ℕ}

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

end TC

end ItoLib

-- ===== F41 =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41
/-! F41 (eq_4_1 work, 986b9ae0, 2026-10-30): zero coordinates stay zero; per-time face invariance. -/
open StochKolmogorov.Persist
variable {n : ℕ}

theorem faceOpen_measurableSet (I : Finset (Fin n)) : MeasurableSet (faceOpen I) := by
  have e : faceOpen I = orthant n ∩ ((⋂ i ∈ (Iᶜ : Finset (Fin n)), {x : SDEState n | x i = 0}) ∩
      (⋂ i ∈ I, {x : SDEState n | 0 < x i})) := by
    ext x; simp [faceOpen]; tauto
  rw [e]
  refine orthant_isClosed.measurableSet.inter (MeasurableSet.inter ?_ ?_)
  · exact Finset.measurableSet_biInter _ fun i _ =>
      (isClosed_eq (PiLp.continuous_apply 2 _ i) continuous_const).measurableSet
  · exact Finset.measurableSet_biInter _ fun i _ =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).measurableSet

/-- Per-time face invariance (lemma_3_1 clause 3 at a fixed time). -/
theorem face_inv1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {I : Finset (Fin n)} {x₀ : SDEState n} (hx₀ : x₀ ∈ faceOpen I) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω ∈ faceOpen I := by
  exact (StochKolmogorov.Persist.kolmogorov_sde_face_invariance C hB hC hx₀ hY).mono fun ω h => h t
/-- The glue form: `P_X(t, x, (ℝ^{I,◦}₊)ᶜ) = 0` for `x ∈ ℝ^{I,◦}₊`. -/
theorem trans_faceOpen_compl {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {I : Finset (Fin n)} {x : SDEState n} (hx : x ∈ faceOpen I) (t : ℝ≥0) :
    StochKolmogorov.Persist.trans P X t x (faceOpen I)ᶜ = 0 := by
  obtain ⟨hP, hB, hX⟩ := hfam
  have hY := hX x hx.1
  unfold StochKolmogorov.Persist.trans
  rw [Measure.map_apply (hY.1 t) (faceOpen_measurableSet I).compl]
  have h := face_inv1 P C B hB hC hx hY t
  rw [ae_iff] at h
  exact h

end F41
end ItoLib

-- ===== HA =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! HA (Harris route, s29): abstract Hairer-Mattingly contraction ("Yet another look at Harris'
ergodic theorem", Thm 3.1) in function form. Drift `QV ≤ γ V + K` plus pairwise overlap
`tvDist (Q x) (Q y) ≤ 1 - α` on `{V x + V y ≤ R}` (`R > 2K/(1-γ)`) make `Q` a strict contraction
for the weighted oscillation `|φ x - φ y| ≤ M (2 + β V x + β V y)`. -/

section HA
variable {X : Type*} [MeasurableSpace X]

theorem abs_sub_le_tvDist (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set X} (hA : MeasurableSet A) :
    |(μ A).toReal - (ν A).toReal| ≤ MarkovChainCLT.tvDist μ ν := by
  refine le_csSup ⟨1, ?_⟩ ⟨A, hA, rfl⟩
  rintro _ ⟨B, -, rfl⟩
  have h1 : (μ B).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := B)); simpa using this
  have h2 : (ν B).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ν) (s := B)); simpa using this
  rw [abs_sub_le_iff]
  constructor <;> linarith [ENNReal.toReal_nonneg (a := μ B), ENNReal.toReal_nonneg (a := ν B)]

end HA
end ItoLib

-- ===== F41b =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! F41b (eq_4_1 work, 986b9ae0, 2026-10-30): uniqueness of invariant probability measures from a
local overlap (Doeblin-on-compacts) condition, via the Jordan parts of `μ - ν`. Pure measure theory. -/

section F41b
variable {X : Type*} [MeasurableSpace X]

/-- Hahn decomposition in restriction form. -/
theorem hahn_restrict_le (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ S : Set X, MeasurableSet S ∧ ν.restrict S ≤ μ.restrict S ∧
      μ.restrict Sᶜ ≤ ν.restrict Sᶜ := by
  obtain ⟨S, hS, hpos, hneg⟩ :=
    (μ.toSignedMeasure - ν.toSignedMeasure).exists_compl_positive_negative
  refine ⟨S, hS, ?_, ?_⟩
  · rw [Measure.le_iff]
    intro A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    have h := VectorMeasure.nonneg_of_zero_le_restrict _
      (VectorMeasure.zero_le_restrict_subset _ hS (Set.inter_subset_right : A ∩ S ⊆ S) hpos)
    rw [Measure.toSignedMeasure_sub_apply (hA.inter hS), measureReal_def, measureReal_def] at h
    rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
    linarith
  · rw [Measure.le_iff]
    intro A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    have h := VectorMeasure.nonpos_of_restrict_le_zero _
      (VectorMeasure.restrict_le_zero_subset _ hS.compl (Set.inter_subset_right : A ∩ Sᶜ ⊆ Sᶜ) hneg)
    rw [Measure.toSignedMeasure_sub_apply (hA.inter hS.compl), measureReal_def,
      measureReal_def] at h
    rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
    linarith

/-- The two Jordan parts satisfy `μ + ζ = ν + η`. -/
theorem jordan_sum (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set X} (hS : MeasurableSet S) (hpos : ν.restrict S ≤ μ.restrict S)
    (hneg : μ.restrict Sᶜ ≤ ν.restrict Sᶜ) :
    μ + (ν.restrict Sᶜ - μ.restrict Sᶜ) = ν + (μ.restrict S - ν.restrict S) := by
  have hη : (μ.restrict S - ν.restrict S) + ν.restrict S = μ.restrict S :=
    Measure.sub_add_cancel_of_le hpos
  have hζ : (ν.restrict Sᶜ - μ.restrict Sᶜ) + μ.restrict Sᶜ = ν.restrict Sᶜ :=
    Measure.sub_add_cancel_of_le hneg
  set η := μ.restrict S - ν.restrict S
  set ζ := ν.restrict Sᶜ - μ.restrict Sᶜ
  calc μ + ζ = (μ.restrict S + μ.restrict Sᶜ) + ζ := by
          rw [Measure.restrict_add_restrict_compl hS]
    _ = μ.restrict S + (ζ + μ.restrict Sᶜ) := by ac_rfl
    _ = μ.restrict S + ν.restrict Sᶜ := by rw [hζ]
    _ = (η + ν.restrict S) + ν.restrict Sᶜ := by rw [hη]
    _ = (ν.restrict S + ν.restrict Sᶜ) + η := by ac_rfl
    _ = ν + η := by rw [Measure.restrict_add_restrict_compl hS]

theorem jordan_mass (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Set X} (hS : MeasurableSet S) (hpos : ν.restrict S ≤ μ.restrict S)
    (hneg : μ.restrict Sᶜ ≤ ν.restrict Sᶜ) :
    (ν.restrict Sᶜ - μ.restrict Sᶜ) univ = (μ.restrict S - ν.restrict S) univ := by
  have h := congrArg (fun m : Measure X => m univ) (jordan_sum μ ν hS hpos hneg)
  simp only [Measure.add_apply, measure_univ] at h
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h

/-- One overlap step: an invariant pair cannot have both Jordan parts charging `K`. -/
theorem jordan_overlap (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Set X} (hS : MeasurableSet S) (hpos : ν.restrict S ≤ μ.restrict S)
    (hneg : μ.restrict Sᶜ ≤ ν.restrict Sᶜ)
    (κ : Kernel X X) [IsMarkovKernel κ] (hμ : μ.bind κ = μ) (hν : ν.bind κ = ν)
    {K : Set X} (hK : MeasurableSet K) {ε : ℝ} (hε : 0 < ε)
    (hov : ∀ x ∈ K, ∀ y ∈ K, MarkovChainCLT.tvDist (κ x) (κ y) ≤ 1 - ε) :
    (μ.restrict S - ν.restrict S) K = 0 ∨ (ν.restrict Sᶜ - μ.restrict Sᶜ) K = 0 := by
  set η := μ.restrict S - ν.restrict S with hηdef
  set ζ := ν.restrict Sᶜ - μ.restrict Sᶜ with hζdef
  have hη : η + ν.restrict S = μ.restrict S := Measure.sub_add_cancel_of_le hpos
  haveI : IsFiniteMeasure η := isFiniteMeasure_of_le (μ.restrict S) Measure.sub_le
  haveI : IsFiniteMeasure ζ := isFiniteMeasure_of_le (ν.restrict Sᶜ) Measure.sub_le
  have hsum : μ + ζ = ν + η := jordan_sum μ ν hS hpos hneg
  have hmass : ζ univ = η univ := jordan_mass μ ν hS hpos hneg
  set a : X → ℝ := fun x => (κ x S).toReal with hadef
  have ha_meas : Measurable a := (κ.measurable_coe hS).ennreal_toReal
  have ha0 : ∀ x, 0 ≤ a x := fun x => ENNReal.toReal_nonneg
  have ha1 : ∀ x, a x ≤ 1 := fun x => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := κ x) (s := S))
    simpa using this
  have hint : ∀ (m : Measure X) [IsFiniteMeasure m], Integrable a m := fun m _ =>
    Integrable.of_bound ha_meas.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ha0 x)]; exact ha1 x)
  have hfin : ∀ (m : Measure X) [IsFiniteMeasure m], ∫⁻ x, κ x S ∂m ≠ ∞ := fun m _ =>
    ne_top_of_le_ne_top (measure_ne_top m univ) (by
      calc ∫⁻ x, κ x S ∂m ≤ ∫⁻ _, 1 ∂m := lintegral_mono fun x => prob_le_one
        _ = m univ := by simp)
  have hIa : ∀ (m : Measure X) [IsFiniteMeasure m], ∫ x, a x ∂m = (∫⁻ x, κ x S ∂m).toReal :=
    fun m _ => integral_toReal (κ.measurable_coe hS).aemeasurable
      (ae_of_all _ fun x => measure_lt_top _ _)
  -- the kernel identity at `S`
  have hk : μ S + ∫⁻ x, κ x S ∂ζ = ν S + ∫⁻ x, κ x S ∂η := by
    have e1 : ∫⁻ x, κ x S ∂μ = μ S := by
      rw [← Measure.bind_apply hS κ.measurable.aemeasurable, hμ]
    have e2 : ∫⁻ x, κ x S ∂ν = ν S := by
      rw [← Measure.bind_apply hS κ.measurable.aemeasurable, hν]
    rw [← e1, ← e2, ← lintegral_add_measure, ← lintegral_add_measure, hsum]
  have hS' : η S + ν S = μ S := by
    have := congrArg (fun m : Measure X => m S) hη
    simpa [Measure.restrict_apply_self] using this
  have hηSc : η Sᶜ = 0 := by
    refine le_antisymm ?_ zero_le
    calc η Sᶜ ≤ μ.restrict S Sᶜ := Measure.sub_le (μ := μ.restrict S) Sᶜ
      _ = 0 := by rw [Measure.restrict_apply hS.compl, compl_inter_self, measure_empty]
  have hηS : η S = η univ := by
    rw [← measure_add_measure_compl hS, hηSc, add_zero]
  -- real form: m = Iη - Iζ
  set m : ℝ := (η univ).toReal with hmdef
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hreal : m = ∫ x, a x ∂η - ∫ x, a x ∂ζ := by
    rw [hIa η, hIa ζ]
    have h1 := congrArg ENNReal.toReal hk
    rw [ENNReal.toReal_add (measure_ne_top _ _) (hfin ζ),
      ENNReal.toReal_add (measure_ne_top _ _) (hfin η)] at h1
    have h2 := congrArg ENNReal.toReal hS'
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hηS] at h2
    linarith
  -- pointwise bound in `y`
  have hy : ∀ y, ∫ x, a x ∂η - m * a y ≤ m - ε * K.indicator 1 y * (η K).toReal := by
    intro y
    have hpt : ∀ x, a x - a y ≤ 1 - ε * K.indicator 1 y * K.indicator 1 x := by
      intro x
      by_cases hx : x ∈ K
      · by_cases hyK : y ∈ K
        · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hyK, Pi.one_apply, mul_one]
          have := abs_sub_le_tvDist (κ x) (κ y) hS
          have h2 := hov x hx y hyK
          have h3 := le_abs_self (a x - a y)
          simp only [hadef] at h3 ⊢
          linarith
        · simp only [Set.indicator_of_notMem hyK, mul_zero, zero_mul, sub_zero]
          linarith [ha1 x, ha0 y]
      · simp only [Set.indicator_of_notMem hx, mul_zero, sub_zero]
        linarith [ha1 x, ha0 y]
    have hL : ∫ x, (a x - a y) ∂η = ∫ x, a x ∂η - m * a y := by
      rw [integral_sub (hint η) (integrable_const _), integral_const, smul_eq_mul, measureReal_def]
    have hR : ∫ x, (1 - ε * K.indicator 1 y * K.indicator 1 x) ∂η =
        m - ε * K.indicator 1 y * (η K).toReal := by
      rw [integral_sub (integrable_const _)
        ((integrable_indicator_iff hK).2 (integrable_const _).integrableOn |>.const_mul _),
        integral_const, smul_eq_mul, mul_one, integral_const_mul, integral_indicator_one hK,
        measureReal_def, measureReal_def]
    rw [← hL, ← hR]
    refine integral_mono ((hint η).sub (integrable_const _)) ?_ hpt
    exact (integrable_const _).sub
      ((integrable_indicator_iff hK).2 (integrable_const _).integrableOn |>.const_mul _)
  -- integrate over `ζ`
  have hζm : (ζ univ).toReal = m := by rw [hmass]
  have hint_y : Integrable (fun y => ∫ x, a x ∂η - m * a y) ζ :=
    (integrable_const _).sub ((hint ζ).const_mul _)
  have hint_y2 : Integrable (fun y => m - ε * K.indicator 1 y * (η K).toReal) ζ := by
    refine (integrable_const _).sub ?_
    have : Integrable (fun y => K.indicator (1 : X → ℝ) y) ζ :=
      (integrable_indicator_iff hK).2 (integrable_const _).integrableOn
    simpa [mul_comm, mul_left_comm, mul_assoc] using this.const_mul (ε * (η K).toReal)
  have hI := integral_mono hint_y hint_y2 hy
  have eL : ∫ y, (∫ x, a x ∂η - m * a y) ∂ζ = m * ∫ x, a x ∂η - m * ∫ y, a y ∂ζ := by
    rw [integral_sub (integrable_const _) ((hint ζ).const_mul _), integral_const, smul_eq_mul,
      measureReal_def, hζm, integral_const_mul]
  have eR : ∫ y, (m - ε * K.indicator 1 y * (η K).toReal) ∂ζ =
      m * m - ε * (η K).toReal * (ζ K).toReal := by
    have : (fun y => m - ε * K.indicator 1 y * (η K).toReal) =
        fun y => m - (ε * (η K).toReal) * K.indicator 1 y := by
      funext y; ring
    rw [this, integral_sub (integrable_const _)
      (((integrable_indicator_iff hK).2 (integrable_const _).integrableOn).const_mul _),
      integral_const, smul_eq_mul, measureReal_def, hζm, integral_const_mul,
      integral_indicator_one hK, measureReal_def]
  rw [eL, eR] at hI
  have hprod : ε * ((η K).toReal * (ζ K).toReal) ≤ 0 := by
    have : m * m = m * (∫ x, a x ∂η - ∫ x, a x ∂ζ) := by rw [← hreal]
    nlinarith
  have hp0 : (η K).toReal * (ζ K).toReal = 0 :=
    le_antisymm (by
      by_contra hc
      push_neg at hc
      have := mul_pos hε hc
      linarith) (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  rcases mul_eq_zero.1 hp0 with h | h
  · left; exact ((ENNReal.toReal_eq_zero_iff _).1 h).resolve_right (measure_ne_top _ _)
  · right; exact ((ENNReal.toReal_eq_zero_iff _).1 h).resolve_right (measure_ne_top _ _)

/-- Uniqueness of invariant probability measures concentrated on `F`, given overlap on an
increasing exhaustion `K j` of `F` (each `K j` with its own Markov kernel leaving both invariant). -/
theorem eq_of_overlap (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : Set X} (hμF : μ Fᶜ = 0) (hνF : ν Fᶜ = 0) (K : ℕ → Set X)
    (hKm : ∀ j, MeasurableSet (K j)) (hKmono : Monotone K) (hcov : F ⊆ ⋃ j, K j)
    (hov : ∀ j, ∃ κ : Kernel X X, IsMarkovKernel κ ∧ μ.bind κ = μ ∧ ν.bind κ = ν ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K j, ∀ y ∈ K j, MarkovChainCLT.tvDist (κ x) (κ y) ≤ 1 - ε) :
    μ = ν := by
  obtain ⟨S, hS, hpos, hneg⟩ := hahn_restrict_le μ ν
  set η := μ.restrict S - ν.restrict S with hηdef
  set ζ := ν.restrict Sᶜ - μ.restrict Sᶜ with hζdef
  have hη : η + ν.restrict S = μ.restrict S := Measure.sub_add_cancel_of_le hpos
  have hζ : ζ + μ.restrict Sᶜ = ν.restrict Sᶜ := Measure.sub_add_cancel_of_le hneg
  have hmass : ζ univ = η univ := jordan_mass μ ν hS hpos hneg
  have hj : ∀ j, η (K j) = 0 ∨ ζ (K j) = 0 := fun j => by
    obtain ⟨κ, hκ, h1, h2, ε, hε, hov⟩ := hov j
    exact jordan_overlap μ ν hS hpos hneg κ h1 h2 (hKm j) hε hov
  have hU : (⋃ j, K j)ᶜ ⊆ Fᶜ := Set.compl_subset_compl.2 hcov
  have hηU : η (⋃ j, K j) = η univ := by
    have h0 : η (⋃ j, K j)ᶜ = 0 := by
      refine le_antisymm ?_ zero_le
      calc η (⋃ j, K j)ᶜ ≤ μ.restrict S (⋃ j, K j)ᶜ := Measure.sub_le (μ := μ.restrict S) _
        _ ≤ μ (⋃ j, K j)ᶜ := Measure.restrict_le_self _
        _ ≤ μ Fᶜ := measure_mono hU
        _ = 0 := hμF
    rw [← measure_add_measure_compl (MeasurableSet.iUnion hKm), h0, add_zero]
  have hζU : ζ (⋃ j, K j) = ζ univ := by
    have h0 : ζ (⋃ j, K j)ᶜ = 0 := by
      refine le_antisymm ?_ zero_le
      calc ζ (⋃ j, K j)ᶜ ≤ ν.restrict Sᶜ (⋃ j, K j)ᶜ := Measure.sub_le (μ := ν.restrict Sᶜ) _
        _ ≤ ν (⋃ j, K j)ᶜ := Measure.restrict_le_self _
        _ ≤ ν Fᶜ := measure_mono hU
        _ = 0 := hνF
    rw [← measure_add_measure_compl (MeasurableSet.iUnion hKm), h0, add_zero]
  have htη : Tendsto (fun j => η (K j)) atTop (𝓝 (η univ)) := by
    rw [← hηU]; exact tendsto_measure_iUnion_atTop hKmono
  have htζ : Tendsto (fun j => ζ (K j)) atTop (𝓝 (ζ univ)) := by
    rw [← hζU]; exact tendsto_measure_iUnion_atTop hKmono
  have hzero : η univ = 0 := by
    by_contra hne
    have hp : 0 < η univ := pos_iff_ne_zero.2 hne
    have hq : 0 < ζ univ := hmass ▸ hp
    obtain ⟨j, hj1, hj2⟩ := ((htη.eventually (eventually_gt_nhds hp)).and
      (htζ.eventually (eventually_gt_nhds hq))).exists
    rcases hj j with h | h
    · exact (ne_of_gt hj1) h
    · exact (ne_of_gt hj2) h
  have hη0 : η = 0 := Measure.measure_univ_eq_zero.1 hzero
  have hζ0 : ζ = 0 := Measure.measure_univ_eq_zero.1 (hmass.trans hzero)
  rw [hη0, zero_add] at hη
  rw [hζ0, zero_add] at hζ
  rw [← Measure.restrict_add_restrict_compl (μ := μ) hS,
    ← Measure.restrict_add_restrict_compl (μ := ν) hS, hη, hζ]

end F41b
end ItoLib

-- ===== U =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M11a
/-! M11a (lemma_3_1 clause 2): pathwise uniqueness for all times at once, and for the Kolmogorov
system. -/

open StochKolmogorov.Persist

end M11a

section M11b
/-! M11b (lemma_3_1 clause 4a): `H < ∞`, i.e. `bracket35` is bounded above on the orthant. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M11b

end ItoLib

-- ===== Y =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12a
/-! M12a: the test-function machinery of V.lean for a single C² nonnegative function `ψ` of a
linear form `ℓ(x) = Σ_k cv_k x_k`, `Φ(x) = ψ(ℓ x)` (used with `ψ ≈ log(1+·)`). -/

variable {Ω : Type*} {d : ℕ}

variable {ψ : ℝ → ℝ} {cv : SDEState d} [hψ : Fact (ContDiff ℝ 2 ψ)] [hψ0 : Fact (∀ v, 0 ≤ ψ v)]

end M12a

section M12b
/-! M12b: the Lyapunov function `log(1 + cᵀx)` for (1.1): `E ∫₀ᵗ w(X_u) du ≤ log(1 + cᵀx) + log 2 + K t`
with `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)` and `K = max H 0` (`H` of (3.5)). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M12b

end ItoLib

-- ===== Z =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12c
/-! M12c: invariant measures integrate the weight `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)`:
`∫ w dμ ≤ max H 0`, hence the Lyapunov integrands `fᵢ − σᵢᵢ gᵢ²/2` are `μ`-integrable. -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- The transition kernel at time `t` (universe-polymorphic copy of `markov_stmt_of_inv`, part 1). -/
theorem kernel_of_family {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    (t : ℝ≥0) :
    ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
      ∀ x ∈ orthant n, κ x = trans P X t x := by
  exact (StochKolmogorov.Persist.markov_property P C B X hfam c γb hA11).1 t
/-- `hint` of `eq_4_1_of_finite`: the Lyapunov integrands are integrable under every invariant `μ`. -/
theorem lyap_integrable (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X) (c : SDEState n) (γb δ₀ : ℝ) (hA : Assumption11 C c γb)
    (hδ : IsDelta0 C γb δ₀) {μ : Measure (SDEState n)} (hμ : IsInvariant P X μ) (i : Fin n) :
    Integrable (fun x => C.f i x - C.sig i i * C.g i x ^ 2 / 2) μ := by
  have hμP := hμ.1
  have hC := hA.2.1
  have hc := hA.2.2.1
  have hδ0 := hδ.1
  have hae : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact hμ.2.1
  obtain ⟨H₁, H₂, -, hH₂, -, h38, -⟩ :=
    StochKolmogorov.Persist.lemma_3_2 hn P C B X hfam c γb hA δ₀ hδ
  have hW := (StochKolmogorov.Persist.lemma_3_3 hn P C B X hfam c γb hA δ₀ hδ H₂ hH₂ h38 μ hμ).1
  have hcont : ContinuousOn (fun x => C.f i x - C.sig i i * C.g i x ^ 2 / 2) (orthant n) :=
    (hC i).1.continuousOn.sub ((continuousOn_const.mul ((hC i).2.continuousOn.pow 2)).div_const 2)
  have hmeas : AEStronglyMeasurable (fun x => C.f i x - C.sig i i * C.g i x ^ 2 / 2) μ := by
    have h := hcont.aestronglyMeasurable (μ := μ) orthant_isClosed.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at h
  refine ⟨hmeas, (hasFiniteIntegral_iff_norm _).2 ?_⟩
  have hσ0 := abs_nonneg (C.sig i i)
  calc ∫⁻ x, ENNReal.ofReal ‖C.f i x - C.sig i i * C.g i x ^ 2 / 2‖ ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (1 + |C.sig i i|) * ENNReal.ofReal ((1 + ∑ k, c k * x k) ^ δ₀ *
          (1 + ∑ k, (|C.f k x| + |C.g k x| ^ 2))) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with x hx
        rw [← ENNReal.ofReal_mul (by linarith), Real.norm_eq_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        have hS : |C.f i x| + |C.g i x| ^ 2 ≤ ∑ k, (|C.f k x| + |C.g k x| ^ 2) :=
          Finset.single_le_sum (f := fun k => |C.f k x| + |C.g k x| ^ 2)
            (fun k _ => by positivity) (Finset.mem_univ i)
        have hb1 : 1 ≤ (1 + ∑ k, c k * x k) ^ δ₀ :=
          Real.one_le_rpow (le_add_of_nonneg_right
            (Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (hx k))) hδ0.le
        have hS0 : 0 ≤ 1 + ∑ k, (|C.f k x| + |C.g k x| ^ 2) := by positivity
        have hg2 : C.g i x ^ 2 = |C.g i x| ^ 2 := (sq_abs _).symm
        have h1 : |C.f i x - C.sig i i * C.g i x ^ 2 / 2| ≤
            |C.f i x| + |C.sig i i| * |C.g i x| ^ 2 := by
          rw [hg2]
          have e : |C.sig i i * |C.g i x| ^ 2 / 2| = |C.sig i i| * |C.g i x| ^ 2 / 2 := by
            rw [abs_div, abs_mul, abs_pow, abs_abs]; norm_num
          have h2 := abs_sub (C.f i x) (C.sig i i * |C.g i x| ^ 2 / 2)
          have h3 : 0 ≤ |C.sig i i| * |C.g i x| ^ 2 := by positivity
          linarith only [h2, e, h3]
        have h4 : |C.f i x| + |C.sig i i| * |C.g i x| ^ 2 ≤
            (1 + |C.sig i i|) * (1 + ∑ k, (|C.f k x| + |C.g k x| ^ 2)) := by
          have h5 : 0 ≤ |C.f i x| := abs_nonneg _
          have h6 : 0 ≤ |C.g i x| ^ 2 := by positivity
          nlinarith only [hS, h5, h6, hσ0]
        have h7 : (1 + |C.sig i i|) * (1 + ∑ k, (|C.f k x| + |C.g k x| ^ 2)) ≤
            (1 + |C.sig i i|) * ((1 + ∑ k, c k * x k) ^ δ₀ *
              (1 + ∑ k, (|C.f k x| + |C.g k x| ^ 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          nlinarith only [hb1, hS0]
        linarith only [h1, h4, h7]
    _ = ENNReal.ofReal (1 + |C.sig i i|) * ∫⁻ x, ENNReal.ofReal ((1 + ∑ k, c k * x k) ^ δ₀ *
          (1 + ∑ k, (|C.f k x| + |C.g k x| ^ 2))) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (1 + |C.sig i i|) * ENNReal.ofReal H₂ := by gcongr
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
end M12c

end ItoLib

-- ===== F41c =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41c
/-! F41c (eq_4_1 work, 986b9ae0, 2026-10-30): boundary ergodic measures live on one open face (E5);
invariant measures on one open face are unique given face overlap (E4 concrete); finiteness of M (E6). -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- The support `{i | 0 < x i}` of a point. -/
noncomputable def supp (x : SDEState n) : Finset (Fin n) := Finset.univ.filter fun i => 0 < x i

theorem mem_faceOpen_supp {x : SDEState n} (hx : x ∈ orthant n) : x ∈ faceOpen (supp x) := by
  refine ⟨hx, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    exact le_antisymm hi (hx i)
  · simpa [supp] using hi

theorem eq_supp_of_mem_faceOpen {I : Finset (Fin n)} {x : SDEState n} (hx : x ∈ faceOpen I) :
    I = supp x := by
  obtain ⟨h0, hz, hp⟩ := hx
  ext i
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact hp i
  · intro h
    by_contra hi
    exact (lt_irrefl _ ((hz i hi) ▸ h))

theorem faceOpen_disjoint {I J : Finset (Fin n)} (hIJ : I ≠ J) : faceOpen I ∩ faceOpen J = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hI hJ
  exact hIJ ((eq_supp_of_mem_faceOpen hI).trans (eq_supp_of_mem_faceOpen hJ).symm)

/-- From a point of the orthant off the face `I`, the face `I` is not charged. -/
theorem trans_face_off {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {I : Finset (Fin n)} {x : SDEState n} (hx : x ∈ orthant n) (hxI : x ∉ faceOpen I) (t : ℝ≥0) :
    trans P X t x (faceOpen I) = 0 := by
  have hJ : supp x ≠ I := fun h => hxI (h ▸ mem_faceOpen_supp hx)
  refine le_antisymm ?_ zero_le
  calc trans P X t x (faceOpen I) ≤ trans P X t x (faceOpen (supp x))ᶜ := by
        refine measure_mono fun y hy hy' => ?_
        have := faceOpen_disjoint hJ
        exact (Set.eq_empty_iff_forall_notMem.1 this) y ⟨hy', hy⟩
    _ = 0 := trans_faceOpen_compl P C B X hfam hC (mem_faceOpen_supp hx) t

/-- Invariance in bind form for a kernel version of `trans`. -/
theorem bind_eq_of_inv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : SDEState n → ℝ≥0 → Ω → SDEState n} {t : ℝ≥0} {κ : Kernel (SDEState n) (SDEState n)}
    (hκx : ∀ x ∈ orthant n, κ x = trans P X t x) {ν : Measure (SDEState n)}
    (hae : ∀ᵐ x ∂ν, x ∈ orthant n)
    (hinv : ∀ A, MeasurableSet A → ∫⁻ x, trans P X t x A ∂ν = ν A) : ν.bind κ = ν := by
  ext A hA
  rw [Measure.bind_apply hA κ.measurable.aemeasurable, ← hinv A hA]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hκx x hx]

/-- The restriction of an invariant measure to an open face is invariant (unnormalized form). -/
theorem restrict_face_inv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    {μ : Measure (SDEState n)} (hμ : IsInvariant P X μ) (I : Finset (Fin n)) (t : ℝ≥0)
    {A : Set (SDEState n)} (hA : MeasurableSet A) :
    ∫⁻ x, trans P X t x A ∂(μ.restrict (faceOpen I)) = μ (A ∩ faceOpen I) := by
  set F := faceOpen I with hF
  have hFm : MeasurableSet F := faceOpen_measurableSet I
  have hae : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact hμ.2.1
  obtain ⟨κ, hκM, hκx⟩ := kernel_of_family P C B X hfam hC hA11 t
  have hbind : μ.bind κ = μ := bind_eq_of_inv hκx hae (hμ.2.2 t)
  have e1 : ∫⁻ x, trans P X t x A ∂(μ.restrict F) = ∫⁻ x, κ x (A ∩ F) ∂(μ.restrict F) := by
    refine lintegral_congr_ae ((ae_restrict_iff' hFm).2 (ae_of_all _ fun x hx => ?_))
    show trans P X t x A = κ x (A ∩ F)
    rw [hκx x hx.1]
    exact (measure_inter_conull (trans_faceOpen_compl P C B X hfam hC hx t)).symm
  have e2 : ∫⁻ x in Fᶜ, κ x (A ∩ F) ∂μ = 0 := by
    rw [show (0 : ℝ≥0∞) = ∫⁻ _ in Fᶜ, 0 ∂μ by simp]
    refine lintegral_congr_ae ((ae_restrict_iff' hFm.compl).2 ?_)
    filter_upwards [hae] with x hx hxF
    rw [hκx x hx]
    exact le_antisymm ((measure_mono Set.inter_subset_right).trans
      (trans_face_off P C B X hfam hC hx hxF t).le) zero_le
  have e3 : ∫⁻ x, κ x (A ∩ F) ∂μ = μ (A ∩ F) := by
    rw [← Measure.bind_apply (hA.inter hFm) κ.measurable.aemeasurable, hbind]
  have e4 := lintegral_add_compl (μ := μ) (fun x => κ x (A ∩ F)) hFm
  rw [e2, add_zero] at e4
  rw [e1, e4, e3]

theorem restrict_face_compl_inv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    {μ : Measure (SDEState n)} (hμ : IsInvariant P X μ) (I : Finset (Fin n)) (t : ℝ≥0)
    {A : Set (SDEState n)} (hA : MeasurableSet A) :
    ∫⁻ x, trans P X t x A ∂(μ.restrict (faceOpen I)ᶜ) = μ (A ∩ (faceOpen I)ᶜ) := by
  haveI := hμ.1
  have hFm : MeasurableSet (faceOpen I) := faceOpen_measurableSet I
  have h1 := restrict_face_inv P C B X hfam hC hA11 hμ I t hA
  have h2 : ∫⁻ x in faceOpen I, trans P X t x A ∂μ + ∫⁻ x in (faceOpen I)ᶜ, trans P X t x A ∂μ =
      μ A := by rw [lintegral_add_compl _ hFm, hμ.2.2 t A hA]
  rw [h1, ← measure_inter_add_diff A hFm, Set.diff_eq] at h2
  exact (ENNReal.add_right_inj (measure_ne_top _ _)).1 h2

/-- E5: a boundary ergodic measure is concentrated on one open face. -/
theorem bdryErgodic_face {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    {μ : Measure (SDEState n)} (hμM : μ ∈ bdryErgodic P X) :
    ∃ I : Finset (Fin n), μ (faceOpen I)ᶜ = 0 := by
  obtain ⟨⟨hinv, hext⟩, -⟩ := hμM
  haveI := hinv.1
  have hcov : orthant n ⊆ ⋃ I : Finset (Fin n), faceOpen I := fun x hx =>
    Set.mem_iUnion.2 ⟨supp x, mem_faceOpen_supp hx⟩
  obtain ⟨I, hIpos⟩ : ∃ I : Finset (Fin n), μ (faceOpen I) ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : μ (orthant n) = 0 := measure_mono_null hcov (measure_iUnion_null h)
    have h1 : μ (orthant n) + μ (orthant n)ᶜ = 1 := by
      rw [measure_add_measure_compl orthant_isClosed.measurableSet, measure_univ]
    rw [h0, hinv.2.1, add_zero] at h1
    exact zero_ne_one h1
  refine ⟨I, ?_⟩
  set F := faceOpen I with hF
  have hFm : MeasurableSet F := faceOpen_measurableSet I
  by_contra hc
  have hF1 : μ F + μ Fᶜ = 1 := by rw [measure_add_measure_compl hFm, measure_univ]
  have hFt : μ F ≠ ∞ := measure_ne_top _ _
  have hFct : μ Fᶜ ≠ ∞ := measure_ne_top _ _
  set ν1 : Measure (SDEState n) := (μ F)⁻¹ • μ.restrict F with hν1
  set ν2 : Measure (SDEState n) := (μ Fᶜ)⁻¹ • μ.restrict Fᶜ with hν2
  have hprob1 : IsProbabilityMeasure ν1 := ⟨by
    rw [hν1, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hIpos hFt]⟩
  have hprob2 : IsProbabilityMeasure ν2 := ⟨by
    rw [hν2, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hc hFct]⟩
  have hinv1 : IsInvariant P X ν1 := by
    refine ⟨hprob1, ?_, fun t A hA => ?_⟩
    · rw [hν1, Measure.smul_apply, Measure.restrict_apply orthant_isClosed.measurableSet.compl,
        measure_mono_null Set.inter_subset_left hinv.2.1, smul_eq_mul, mul_zero]
    · rw [hν1, lintegral_smul_measure, restrict_face_inv P C B X hfam hC hA11 hinv I t hA,
        Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  have hinv2 : IsInvariant P X ν2 := by
    refine ⟨hprob2, ?_, fun t A hA => ?_⟩
    · rw [hν2, Measure.smul_apply, Measure.restrict_apply orthant_isClosed.measurableSet.compl,
        measure_mono_null Set.inter_subset_left hinv.2.1, smul_eq_mul, mul_zero]
    · rw [hν2, lintegral_smul_measure, restrict_face_compl_inv P C B X hfam hC hA11 hinv I t hA,
        Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  set a : ℝ≥0 := (μ F).toNNReal with ha
  have haF : (a : ℝ≥0∞) = μ F := ENNReal.coe_toNNReal hFt
  have ha0 : 0 < a := by
    rw [← ENNReal.coe_lt_coe, haF, ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hIpos
  have ha1 : a < 1 := by
    rw [← ENNReal.coe_lt_coe, haF, ENNReal.coe_one]
    have : μ Fᶜ ≠ 0 := hc
    have h2 : 0 < μ Fᶜ := pos_iff_ne_zero.2 this
    calc μ F = μ F + 0 := (add_zero _).symm
      _ < μ F + μ Fᶜ := ENNReal.add_lt_add_left hFt h2
      _ = 1 := hF1
  have h1a : ((1 - a : ℝ≥0) : ℝ≥0∞) = μ Fᶜ := by
    rw [ENNReal.coe_sub, ENNReal.coe_one, haF, prob_compl_eq_one_sub hFm]
  have hdec : μ = (a : ℝ≥0∞) • ν1 + ((1 - a : ℝ≥0) : ℝ≥0∞) • ν2 := by
    rw [haF, h1a, hν1, hν2, smul_smul, smul_smul, ENNReal.mul_inv_cancel hIpos hFt,
      ENNReal.mul_inv_cancel hc hFct, one_smul, one_smul, Measure.restrict_add_restrict_compl hFm]
  have heq := hext ν1 ν2 hinv1 hinv2 a ha0 ha1 hdec
  apply hc
  rw [← heq, hν1, Measure.smul_apply, Measure.restrict_apply hFm.compl, Set.compl_inter_self,
    measure_empty, smul_eq_mul, mul_zero]

/-- The compact pieces of an open face. -/
def faceBox (I : Finset (Fin n)) (α β : ℝ) : Set (SDEState n) :=
  {x | x ∈ faceOpen I ∧ ∀ i ∈ I, α ≤ x i ∧ x i ≤ β}

theorem faceBox_measurableSet (I : Finset (Fin n)) (α β : ℝ) : MeasurableSet (faceBox I α β) := by
  have e : faceBox I α β = faceOpen I ∩
      ⋂ i ∈ I, ({x : SDEState n | α ≤ x i} ∩ {x : SDEState n | x i ≤ β}) := by
    ext x; simp [faceBox, Set.mem_iInter₂]
  rw [e]
  exact (faceOpen_measurableSet I).inter (Finset.measurableSet_biInter _ fun i _ =>
    (measurableSet_le measurable_const (PiLp.continuous_apply 2 _ i).measurable).inter
    (measurableSet_le (PiLp.continuous_apply 2 _ i).measurable measurable_const))

theorem tvDist_self' {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) :
    MarkovChainCLT.tvDist μ μ = 0 := by
  unfold MarkovChainCLT.tvDist
  have : {r : ℝ | ∃ A : Set Y, MeasurableSet A ∧ r = |(μ A).toReal - (μ A).toReal|} = {0} := by
    ext r
    simp only [sub_self, abs_zero, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨∅, MeasurableSet.empty, h⟩⟩
  rw [this, csSup_singleton]

theorem eq_zero_of_mem_faceOpen_empty {x : SDEState n} (hx : x ∈ faceOpen (∅ : Finset (Fin n))) :
    x = 0 := by
  ext i
  simpa using hx.2.1 i (Finset.notMem_empty i)

/-- The (trivial) overlap on the vertex face `{0}`. -/
theorem face_overlap_empty {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (α β : ℝ) :
    ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ faceBox (∅ : Finset (Fin n)) α β,
      ∀ y ∈ faceBox (∅ : Finset (Fin n)) α β,
        MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε := by
  refine ⟨0, 1 / 2, by norm_num, fun x hx y hy => ?_⟩
  rw [eq_zero_of_mem_faceOpen_empty hx.1, eq_zero_of_mem_faceOpen_empty hy.1, tvDist_self']
  norm_num

/-- E4 (concrete): invariant probability measures on one open face coincide, given overlap on
the face boxes. -/
theorem inv_unique_face {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    {I : Finset (Fin n)}
    (hov : ∀ α β : ℝ, 0 < α → α ≤ β → ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ faceBox I α β,
      ∀ y ∈ faceBox I α β, MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε)
    {μ ν : Measure (SDEState n)} (hμ : IsInvariant P X μ) (hν : IsInvariant P X ν)
    (hμF : μ (faceOpen I)ᶜ = 0) (hνF : ν (faceOpen I)ᶜ = 0) : μ = ν := by
  haveI := hμ.1
  haveI := hν.1
  have haeμ : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact hμ.2.1
  have haeν : ∀ᵐ x ∂ν, x ∈ orthant n := by rw [ae_iff]; exact hν.2.1
  refine eq_of_overlap μ ν hμF hνF (fun j : ℕ => faceBox I (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1))
    (fun j => faceBox_measurableSet _ _ _) ?_ ?_ ?_
  · intro j k hjk x hx
    have hjk' : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).2 hjk; linarith
    refine ⟨hx.1, fun i hi => ⟨le_trans ?_ (hx.2 i hi).1, (hx.2 i hi).2.trans hjk'⟩⟩
    exact one_div_le_one_div_of_le (by positivity) hjk'
  · intro x hx
    have hev : ∀ᶠ j : ℕ in atTop, ∀ i ∈ I, 1 / ((j : ℝ) + 1) ≤ x i ∧ x i ≤ (j : ℝ) + 1 := by
      refine (Filter.eventually_all_finset I).2 fun i hi => ?_
      have hxi : 0 < x i := hx.2.2 i hi
      refine ((tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hxi)).and
        (tendsto_natCast_atTop_atTop.eventually_ge_atTop (x i))).mono fun j hj => ⟨hj.1.le, ?_⟩
      linarith [hj.2]
    obtain ⟨j, hj⟩ := hev.exists
    exact Set.mem_iUnion.2 ⟨j, hx, hj⟩
  · intro j
    have hα : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hαβ : 1 / ((j : ℝ) + 1) ≤ (j : ℝ) + 1 := by
      have h1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; have := (j.cast_nonneg : (0 : ℝ) ≤ j); linarith
      have := (j.cast_nonneg : (0 : ℝ) ≤ j); linarith
    obtain ⟨T, ε, hε, h⟩ := hov _ _ hα hαβ
    obtain ⟨κ, hκM, hκx⟩ := kernel_of_family P C B X hfam hC hA11 T
    refine ⟨κ, hκM, bind_eq_of_inv hκx haeμ (hμ.2.2 T), bind_eq_of_inv hκx haeν (hν.2.2 T),
      ε, hε, fun x hx y hy => ?_⟩
    rw [hκx x hx.1.1, hκx y hy.1.1]
    exact h x hx y hy

/-- E6: `M` is finite, given overlap on the boxes of every nonempty open face. -/
theorem bdryErgodic_finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    (hov : ∀ I : Finset (Fin n), I.Nonempty → ∀ α β : ℝ, 0 < α → α ≤ β → ∃ T : ℝ≥0, ∃ ε : ℝ,
      0 < ε ∧ ∀ x ∈ faceBox I α β, ∀ y ∈ faceBox I α β,
        MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε) :
    (bdryErgodic P X).Finite := by
  have hsub : bdryErgodic P X ⊆
      ⋃ I : Finset (Fin n), {μ | μ ∈ bdryErgodic P X ∧ μ (faceOpen I)ᶜ = 0} := fun μ hμ => by
    obtain ⟨I, hI⟩ := bdryErgodic_face P C B X hfam hC hA11 hμ
    exact Set.mem_iUnion.2 ⟨I, hμ, hI⟩
  refine Set.Finite.subset (Set.finite_iUnion fun I => Set.Subsingleton.finite ?_) hsub
  rintro μ ⟨hμ, hμF⟩ ν ⟨hν, hνF⟩
  have hovI : ∀ α β : ℝ, 0 < α → α ≤ β → ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ faceBox I α β,
      ∀ y ∈ faceBox I α β, MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε := by
    intro α β hα hαβ
    by_cases hI : I.Nonempty
    · exact hov I hI α β hα hαβ
    · rw [Finset.not_nonempty_iff_eq_empty.1 hI]
      exact face_overlap_empty P X α β
  exact inv_unique_face P C B X hfam hC hA11 hovI hμ.1.1 hν.1.1 hμF hνF

end F41c
end ItoLib

-- ===== X41 =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! X41 (eq_4_1, finite-`M` part): the minimax step of [SBA11, Lemma 4] for finitely many
boundary ergodic measures, by strict separation of a polytope from the closed negative orthant. -/

/-- Finite minimax: if every convex combination of `v μ` (finitely many `μ`) has a positive
coordinate, a strictly positive weight vector of total mass `δ₀` is positive on every `v μ`. -/
theorem exists_pos_weight {n : ℕ} (hn : 0 < n) {κ : Type*} [Fintype κ] (v : κ → (Fin n → ℝ))
    (hV : ∀ w ∈ stdSimplex ℝ κ, ∃ i, 0 < ∑ μ, w μ * v μ i) (δ₀ : ℝ) (hδ : 0 < δ₀) :
    ∃ p : Fin n → ℝ, (∀ i, 0 < p i) ∧ ∑ i, p i = δ₀ ∧ ∀ μ, 0 < ∑ i, p i * v μ i := by
  classical
  set L : (κ → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Fintype.linearCombination ℝ v with hL
  set K : Set (Fin n → ℝ) := L '' stdSimplex ℝ κ with hK
  set Cn : Set (Fin n → ℝ) := {y | ∀ i, y i ≤ 0} with hCn
  have hKc : IsCompact K := (isCompact_stdSimplex ℝ κ).image L.continuous_of_finiteDimensional
  have hKv : Convex ℝ K := (convex_stdSimplex ℝ κ).linear_image L
  have hCv : Convex ℝ Cn := by
    intro a ha b hb s t hs ht _ i
    simp only [Cn, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    nlinarith [ha i, hb i, mul_nonneg hs (neg_nonneg.2 (ha i)), mul_nonneg ht (neg_nonneg.2 (hb i))]
  have hCc : IsClosed Cn := by
    have : Cn = ⋂ i, {y : Fin n → ℝ | y i ≤ 0} := by ext y; simp [Cn]
    rw [this]
    exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
  have hdisj : Disjoint K Cn := by
    rw [Set.disjoint_left]
    rintro y ⟨w, hw, rfl⟩ hc
    obtain ⟨i, hi⟩ := hV w hw
    have := hc i
    simp only [hL, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at this
    linarith
  obtain ⟨f, u, w, hfu, huw, hfw⟩ := geometric_hahn_banach_compact_closed hKv hKc hCv hCc hdisj
  have h0 : (0 : Fin n → ℝ) ∈ Cn := fun i => le_refl _
  have hw0 : w < 0 := by simpa using hfw 0 h0
  have hcone : ∀ y ∈ Cn, 0 ≤ f y := by
    intro y hy
    by_contra hneg
    push Not at hneg
    have hty : (2 * w / f y) • y ∈ Cn := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg_of_nonpos (by linarith) hneg.le) (hy i)
    have := hfw _ hty
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    linarith
  -- coefficients `q i = f (-e_i) ≥ 0`
  set e : Fin n → (Fin n → ℝ) := fun i j => if i = j then 1 else 0 with he
  set q : Fin n → ℝ := fun i => - f (e i) with hq
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i
    have : -(e i) ∈ Cn := fun j => by simp only [he, Pi.neg_apply]; split_ifs <;> norm_num
    have := hcone _ this
    simpa [hq, map_neg] using this
  have hf : ∀ y, f y = - ∑ i, q i * y i := by
    intro y
    conv_lhs => rw [pi_eq_sum_univ y]
    simp only [map_sum, map_smul, smul_eq_mul, hq, he]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hpos : ∀ μ, 0 < ∑ i, q i * v μ i := by
    intro μ
    have hmem : v μ ∈ K := by
      refine ⟨fun ν => if ν = μ then 1 else 0, ?_, ?_⟩
      · refine ⟨fun ν => by dsimp only; split_ifs <;> norm_num, ?_⟩
        simp
      · simp [hL, Fintype.linearCombination_apply]
    have := hfu _ hmem
    rw [hf] at this
    linarith
  -- perturb to strictly positive weights
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ μ, 0 < ∑ i, (q i + ε) * v μ i := by
    rw [Filter.eventually_all]
    intro μ
    have hc : Continuous fun ε : ℝ => ∑ i, (q i + ε) * v μ i := by fun_prop
    have h0' : 0 < (fun ε : ℝ => ∑ i, (q i + ε) * v μ i) 0 := by simpa using hpos μ
    exact (hc.continuousAt.eventually (lt_mem_nhds h0')).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hε, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hεpos' : (0 : ℝ) < ε := hεpos
  set S : ℝ := ∑ i, (q i + ε) with hS
  have hSpos : 0 < S := by
    have : ∑ _i : Fin n, ε ≤ S := Finset.sum_le_sum fun i _ => by linarith [hq0 i]
    have h1 : 0 < ∑ _i : Fin n, ε := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_pos (by exact_mod_cast hn) hεpos'
    linarith
  refine ⟨fun i => δ₀ / S * (q i + ε), fun i => ?_, ?_, fun μ => ?_⟩
  · exact mul_pos (div_pos hδ hSpos) (by linarith [hq0 i])
  · rw [← Finset.mul_sum, ← hS, div_mul_cancel₀ _ hSpos.ne']
  · have : ∑ i, δ₀ / S * (q i + ε) * v μ i = δ₀ / S * ∑ i, (q i + ε) * v μ i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact mul_pos (div_pos hδ hSpos) (hε μ)

/-- `exists_pos_weight` for a finite set `s` of an arbitrary type, weights indexed by `ι`. -/
theorem exists_pos_weight_finset {n : ℕ} (hn : 0 < n) {ι : Type*} (s : Finset ι)
    (v : ι → (Fin n → ℝ))
    (hV : ∀ w : ι → ℝ, (∀ μ ∈ s, 0 ≤ w μ) → ∑ μ ∈ s, w μ = 1 → ∃ i, 0 < ∑ μ ∈ s, w μ * v μ i)
    (δ₀ : ℝ) (hδ : 0 < δ₀) :
    ∃ p : Fin n → ℝ, (∀ i, 0 < p i) ∧ ∑ i, p i = δ₀ ∧ ∀ μ ∈ s, 0 < ∑ i, p i * v μ i := by
  classical
  obtain ⟨p, hp, hps, hpv⟩ := exists_pos_weight hn (fun μ : s => v μ) (fun w hw => by
    obtain ⟨i, hi⟩ := hV (fun μ => if h : μ ∈ s then w ⟨μ, h⟩ else 0)
      (fun μ hμ => by simp only [dif_pos hμ]; exact hw.1 _)
      (by rw [← Finset.sum_coe_sort s]; simpa using hw.2)
    refine ⟨i, ?_⟩
    rw [← Finset.sum_coe_sort s] at hi
    simpa using hi) δ₀ hδ
  exact ⟨p, hp, hps, fun μ hμ => hpv ⟨μ, hμ⟩⟩

open StochKolmogorov.Persist EthierKurtz in
/-- `lyap` is affine on finite combinations of measures integrating the Lyapunov integrand. -/
theorem lyap_finset_sum {n : ℕ} (C : Coeffs n) (i : Fin n) {ι : Type*} (t : Finset ι)
    (ν : ι → Measure (SDEState n)) (a : ι → ℝ≥0)
    (hint : ∀ μ ∈ t, Integrable (fun x => C.f i x - C.sig i i * C.g i x ^ 2 / 2) (ν μ)) :
    lyap C i (∑ μ ∈ t, (a μ : ℝ≥0∞) • ν μ) = ∑ μ ∈ t, (a μ : ℝ) * lyap C i (ν μ) := by
  unfold lyap
  rw [integral_finsetSum_measure fun μ hμ => (hint μ hμ).smul_measure ENNReal.coe_ne_top]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]

open StochKolmogorov.Persist EthierKurtz in
/-- (4.1) when `M` is finite and every `μ ∈ M` integrates the Lyapunov integrands. -/
theorem eq_4_1_of_finite {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfin : (bdryErgodic P X).Finite) (hne : (bdryErgodic P X).Nonempty)
    (hint : ∀ μ ∈ bdryErgodic P X, ∀ i,
      Integrable (fun x => C.f i x - C.sig i i * C.g i x ^ 2 / 2) μ)
    (h12 : Assumption12 P C X) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ p ∈ openOrthant n, l1 p = δ₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ IsWeightedInvasionMin P C X p ρ := by
  classical
  set s := hfin.toFinset with hs
  have hsM : ∀ μ, μ ∈ s ↔ μ ∈ bdryErgodic P X := fun μ => hfin.mem_toFinset
  obtain ⟨p, hp, hps, hpv⟩ := exists_pos_weight_finset hn s (fun μ i => lyap C i μ) (by
    intro w hw0 hw1
    set t := s.filter (fun μ => 0 < w μ) with ht
    set π : Measure (SDEState n) := ∑ μ ∈ t, ((w μ).toNNReal : ℝ≥0∞) • μ with hπ
    have htsum : ∑ μ ∈ t, w μ = 1 := by
      rw [ht, Finset.sum_filter_of_ne]; · exact hw1
      intro μ hμ hne; exact lt_of_le_of_ne (hw0 μ hμ) (Ne.symm hne)
    have hπc : π ∈ conv (bdryErgodic P X) := by
      refine ⟨t, fun μ => (w μ).toNNReal, ?_, ?_, ?_, rfl⟩
      · intro μ hμ
        exact (hsM μ).1 (Finset.mem_of_mem_filter μ hμ)
      · intro μ hμ
        exact Real.toNNReal_pos.2 (Finset.mem_filter.1 hμ).2
      · apply NNReal.eq
        rw [NNReal.coe_sum, NNReal.coe_one, ← htsum]
        refine Finset.sum_congr rfl fun μ hμ => ?_
        exact Real.coe_toNNReal _ (Finset.mem_filter.1 hμ).2.le
    obtain ⟨i, hi⟩ := h12 π hπc
    refine ⟨i, ?_⟩
    rw [hπ, lyap_finset_sum C i t (fun μ => μ) (fun μ => (w μ).toNNReal)
      (fun μ hμ => hint μ ((hsM μ).1 (Finset.mem_of_mem_filter μ hμ)) i)] at hi
    have : ∑ μ ∈ t, ((w μ).toNNReal : ℝ) * lyap C i μ = ∑ μ ∈ s, w μ * lyap C i μ := by
      rw [ht, Finset.sum_filter_of_ne]
      · refine Finset.sum_congr rfl fun μ hμ => ?_
        rw [Real.coe_toNNReal _ (hw0 μ hμ)]
      · intro μ hμ hne
        refine lt_of_le_of_ne (hw0 μ hμ) (Ne.symm fun h => hne ?_)
        rw [h]; simp
    linarith) δ₀ hδ₀
  obtain ⟨μ0, hμ0, hmin⟩ := s.exists_min_image (fun μ => ∑ i, p i * lyap C i μ)
    (by obtain ⟨μ, hμ⟩ := hne; exact ⟨μ, (hsM μ).2 hμ⟩)
  refine ⟨WithLp.toLp 2 p, fun i => by simpa using hp i, ?_, (∑ i, p i * lyap C i μ0) / 2,
    by linarith [hpv μ0 hμ0], ?_, ?_⟩
  · unfold l1
    rw [← hps]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [abs_of_pos (hp i)]
  · intro μ hμ
    have := hmin μ ((hsM μ).2 hμ)
    simp only [PiLp.toLp_apply]
    linarith
  · refine ⟨μ0, (hsM μ0).1 hμ0, ?_⟩
    simp only [PiLp.toLp_apply]
    ring

open StochKolmogorov.Persist EthierKurtz in
/-- `δ₀` of (3.2) exists: `δ₀ = γ_b / (3 S n + 3)` with `S = ∑ᵢⱼ |σᵢⱼ|`. -/
theorem exists_isDelta0 {n : ℕ} (C : Coeffs n) (γb : ℝ) (hγ : 0 < γb) :
    ∃ δ₀ : ℝ, IsDelta0 C γb δ₀ := by
  set S : ℝ := ∑ i, ∑ j, |C.sig i j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsij : ∀ i j, |C.sig i j| ≤ S := by
    intro i j
    calc |C.sig i j| ≤ ∑ j', |C.sig i j'| :=
          Finset.single_le_sum (f := fun j' => |C.sig i j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', |C.sig i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hden : 0 < 3 * S * n + 3 := by positivity
  refine ⟨γb / (3 * S * n + 3), div_pos hγ hden, ?_, fun x _ => ?_⟩
  · rw [div_lt_div_iff₀ hden two_pos]
    nlinarith [mul_nonneg hS0 (Nat.cast_nonneg (α := ℝ) n)]
  · set δ := γb / (3 * S * n + 3) with hδ
    have hδ0 : 0 ≤ δ := (div_pos hγ hden).le
    set G : ℝ := ∑ i, C.g i x ^ 2 with hG
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hterm : ∀ i j, |C.g i x * C.g j x * C.sig i j|
        ≤ S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by
      intro i j
      rw [abs_mul, abs_mul]
      have h1 : |C.g i x| * |C.g j x| ≤ (C.g i x ^ 2 + C.g j x ^ 2) / 2 := by
        nlinarith [sq_nonneg (|C.g i x| - |C.g j x|), sq_abs (C.g i x), sq_abs (C.g j x)]
      calc |C.g i x| * |C.g j x| * |C.sig i j| ≤ ((C.g i x ^ 2 + C.g j x ^ 2) / 2) * S :=
            mul_le_mul h1 (hsij i j) (abs_nonneg _) (by positivity)
        _ = S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by ring
    have hsum : ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| ≤ S * n * G := by
      calc ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
          ≤ ∑ i : Fin n, ∑ j : Fin n, S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = S * n * G := by
            simp only [← Finset.mul_sum, add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hG, ← Finset.sum_div]
            ring
    have hkey : δ * (3 * S * n + 3) = γb := by rw [hδ, div_mul_cancel₀ _ hden.ne']
    calc 3 * δ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| + δ * G
        ≤ 3 * δ * (S * n * G) + δ * G := by nlinarith
      _ ≤ δ * (3 * S * n + 3) * G := by nlinarith [mul_nonneg hδ0 hG0]
      _ = γb * G := by rw [hkey]

end ItoLib

-- ===== F41d =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41d
/-! F41d (eq_4_1 work, 986b9ae0, 2026-10-30): eq_4_1 from the face overlap property. -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- `δ₀ ∈ M` (copy of D.dirac_check through per-time face invariance, so D is not imported). -/
theorem dirac_mem_bdryErgodic (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Measure.dirac (0 : SDEState n) ∈ bdryErgodic P X := by
  have h0 : (0 : SDEState n) ∈ orthant n := fun i => by simp
  have h0F : (0 : SDEState n) ∈ faceOpen (∅ : Finset (Fin n)) :=
    ⟨h0, fun i _ => by simp, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  have htr : ∀ t, trans P X t 0 = Measure.dirac 0 := by
    intro t
    haveI := hX.1
    haveI : IsProbabilityMeasure (trans P X t 0) :=
      Measure.isProbabilityMeasure_map ((hX.2.2 0 h0).1 t).aemeasurable
    have hc : trans P X t 0 {(0 : SDEState n)}ᶜ = 0 := by
      refine measure_mono_null ?_ (trans_faceOpen_compl P C B X hX hC h0F t)
      intro y hy hyF
      exact hy (eq_zero_of_mem_faceOpen_empty hyF)
    have hae : ∀ᵐ x ∂(trans P X t 0), x ∈ ({0} : Set (SDEState n)) := ae_iff.2 hc
    have h1 : trans P X t 0 {(0 : SDEState n)} = 1 :=
      (prob_compl_eq_zero_iff (measurableSet_singleton _)).1 hc
    calc trans P X t 0 = (trans P X t 0).restrict {0} :=
          (Measure.restrict_eq_self_of_ae_mem hae).symm
      _ = Measure.dirac 0 := by rw [Measure.restrict_singleton, h1, one_smul]
  have hinv : IsInvariant P X (Measure.dirac 0) := by
    refine ⟨inferInstance, ?_, fun t A _ => ?_⟩
    · rw [Measure.dirac_apply]; simp [h0]
    · rw [lintegral_dirac, htr]
  refine ⟨⟨hinv, fun ν₁ ν₂ h₁ _ a ha0 _ heq => ?_⟩, ?_⟩
  · have := h₁.1
    have hc : ν₁ {(0 : SDEState n)}ᶜ = 0 := by
      have := congrArg (fun μ : Measure (SDEState n) => μ {(0 : SDEState n)}ᶜ) heq
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at this
      have hd : Measure.dirac (0 : SDEState n) {(0 : SDEState n)}ᶜ = 0 := by
        simp [Measure.dirac_apply]
      rw [hd] at this
      have h1 := (add_eq_zero.1 this.symm).1
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd (ENNReal.coe_eq_zero.1 h) ha0.ne'
      · exact h
    have hae : ∀ᵐ x ∂ν₁, x ∈ ({0} : Set (SDEState n)) := ae_iff.2 hc
    have h1 : ν₁ {(0 : SDEState n)} = 1 :=
      (prob_compl_eq_zero_iff (measurableSet_singleton _)).1 hc
    calc ν₁ = ν₁.restrict {0} := (Measure.restrict_eq_self_of_ae_mem hae).symm
      _ = Measure.dirac 0 := by rw [Measure.restrict_singleton, h1, one_smul]
  · have hno : (0 : SDEState n) ∉ openOrthant n := fun h => by
      have := h ⟨0, hn⟩; simp at this
    rw [Measure.dirac_apply]
    simp [hno]

/-- eq_4_1 given the face overlap property (E3, open). -/
theorem eq_4_1_of_face_overlap (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h12 : Assumption12 P C X) (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hov : ∀ I : Finset (Fin n), I.Nonempty → ∀ α β : ℝ, 0 < α → α ≤ β → ∃ T : ℝ≥0, ∃ ε : ℝ,
      0 < ε ∧ ∀ x ∈ faceBox I α β, ∀ y ∈ faceBox I α β,
        MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε) :
    ∃ p ∈ openOrthant n, l1 p = δ₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ IsWeightedInvasionMin P C X p ρ := by
  have hC := hA.2.1
  obtain ⟨δ', hδ'⟩ := exists_isDelta0 C γb hA.2.2.2.1
  exact eq_4_1_of_finite hn P C X (bdryErgodic_finite P C B X hX hC hA hov)
    ⟨_, dirac_mem_bdryErgodic hn P C B X hX hC⟩
    (fun μ hμ i => lyap_integrable hn P C B X hX c γb δ' hA hδ' hμ.1.1 i) h12 δ₀ hδ₀

end F41d
end ItoLib

-- ===== CB =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CB (CORE route C2, s22): Cameron-Martin shift formula for centered Gaussians, one-dimensional
and for finite independent families (`Measure.pi`). -/

end ItoLib

-- ===== CC =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C2b
/-! CORE route C2b (s23): one-cell Cameron-Martin for the cell noise `(ξ, ζ)` with a constant shift:
weighting by `cmwPi h u ξ` and shifting `(ξ, ζ) ↦ (ξ + u, ζ + u/2)` preserves the law.
Route: dyadic increments are i.i.d. `N(0, h/2^n)` (`dInc_law`), the dyadic approximation of the
noise is a linear function `psiN` of them (`apx_eq_psiN`), finite-dimensional Cameron-Martin
(`gauss_pi_shift`) at each level, then the limit `n → ∞`. -/

end C2b

end ItoLib

-- ===== CD =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C3
/-! CORE route C3 (s23): adapted discrete Girsanov over the cells. The first `k` cell noises have
law `ν_k = ν_{k-1} ⊗ ν_1` (independence of the past and time homogeneity); shifting cell `l` by
`(u_l, u_l/2)` with `u_l` a measurable function of the earlier noises and weighting by
`∏ cmwPi h u_l ξ_l` preserves `ν_k` (`girsanov_cells`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end C3

end ItoLib

-- ===== CE =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {d : ℕ}

section C4a
/-! CORE route C4a (s23): the steered coupling, deterministic part. Two copies of the scheme are run
on one noise sequence; the second copy uses the shifted noise `n + (u, u/2)` with the adapted
steering `u_l = J(Ŷ pair)((X_l - Ŷ_l)/(m - l))`. The shift adds `avgApply p u` to a step
(`zstep_shift`), so with a right inverse `J` of `avgApply` the step adds `(X_l - Ŷ_l)/(m - l)`
(`cstep_steer`). The steered copy is the plain scheme driven by `shV (steerN ..)` (`shV_crec`). -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)

variable {s₁ b₁ h J m}

end C4a

end ItoLib

-- ===== CF =====
open Filter Set
open scoped BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CORE route C4b (s23): the steered second-moment recursion. If
`e_{k+1} ≤ (1 - 1/(m-k))² e_k + c h (e_k + e_{k-1})` (with `e_{-1}` given by `e' 0`), then
`e_k ≤ G ((m-k)/m)² (1 + 13 c h)^k` for `k < m`. Key fact: `(j+1)² + (j+2)² ≤ 13 j²` for `j ≥ 1`. -/

end ItoLib

-- ===== CG =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C4c
/-! CORE route C4c (s24): the steered coupling driven by a Brownian motion. Past-measurability of
the coupled chain, the one-step identity `D_{k+1} = (1 - 1/(m-k)) D_k + h/2 Δb + cellNoise`,
and the second-moment step feeding `steer_rec` (CF.lean). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4c

end ItoLib

-- ===== CH =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
variable {Ω : Type*}

section C4d
/-! CORE route C4d (s24): lower bound of a weighted event by the relative entropy, with no second
moment of the Girsanov martingale. If `f > 0`, `E f ≤ 1` and `E[-log f] ≤ K`, then
`E[1_E f] ≥ e^{-a} (P E - (K+1)/a)` (Markov on `-log f + f ≥ (-log f)⁺`). -/

end C4d

section C4d2
/-! C4d (s25): the relative entropy of the steering weight. -/
open EthierKurtz

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4d2

end ItoLib

-- ===== CI =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
set_option autoImplicit false

namespace ItoLib

section C5a
/-! CORE route C5a (s25): Kolmogorov's maximal inequality in the abstract form needed for the
exit estimate of the Euler chain. The only probabilistic input is the orthogonality of the
"stopped" value `1_{F_k} M_k` to the remaining increment `M_m - M_k`. -/

variable {Ω : Type*} {d : ℕ}

end C5a

end ItoLib

-- ===== CK =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5c
/-! CORE route C5c (s26): exit estimate for the Euler chain with bounded coefficients.
`Z_k = Z_0 + M_k + D_k` with `M` the martingale part (orthogonal cell increments) and `D` the
drift part (`‖D_k‖ ≤ k h S`); Kolmogorov's maximal inequality on `M` gives
`(δ/2)^2 P(∃ k ≤ m, ‖Z_k - Z_0‖ ≥ δ) ≤ 16 d S^2 m h` once `m h S ≤ δ/2`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end C5c
end ItoLib

-- ===== CL =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5d
/-! CORE route C5d (s26): a global, measurable, bounded right inverse of `avgApply` for diffusions
of the form `s x (i, j) = a i x * Γ j i` (the Kolmogorov diffusion read through a projection),
when `Γ` is invertible and `|a i x + a i y| ≥ κ > 0`. -/

variable {d : ℕ}

end C5d
end ItoLib

-- ===== CM =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5dK
/-! CORE route C5d, Kolmogorov instance (s26): the coefficients read through the box clamp
`boxP α β` (box `[α, β]^n` inside the open orthant) are globally Lipschitz and bounded, have the
form `s x (i, j) = aK i x * Γ j i`, and `|aK i x + aK i y| ≥ κ > 0` (Assumption 1.1 part 1). -/

variable {n : ℕ}

open StochKolmogorov.Persist

end C5dK
end ItoLib

-- ===== CN =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5g
/-! CORE route, s27: (1) `Γ` is invertible under Assumption 1.1 part 1; (2) a generic discrete
martingale `gmart` built from bounded past-measurable cell coefficients: measurability, second
moment, orthogonality and the Kolmogorov maximal inequality (used for the tracking estimate of
the steered chain). -/

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0} {A B : ℕ → Ω → SDEDiffusion d}

end C5g
end ItoLib

-- ===== CO =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5t
/-! CORE route, s27: tracking estimate for the steered coupling. With `D_k = X_k - Ŷ_k`,
`D_k - ((m-k)/m) D_0 = (m-k) (Σ_{l<k} w_l Δb_l + gmart_k)` (weights `w_l = 1/(m-l-1)`), so a
maximal inequality on `gmart` plus a second-moment bound on the drift sum control
`max_{k ≤ m-1} ‖D_k - ((m-k)/m) D_0‖`. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d)
  (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)
  (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0)
  (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d))

variable {s₁ b₁ J m}

end C5t
end ItoLib

-- ===== CP =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5u
/-! CORE route, s28: explicit O(T) form of the tracking estimate (T = m h). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0}

end C5u
end ItoLib

-- ===== CQ =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5v
/-! CORE route, s28: discrete Girsanov for PATH events. The law of the plain path from `q₀.2` on a
path set `Ap` is at least `e^{-a}` times the probability that the STEERED path `Ŷ_k = (cq k).2.2`
lies in `Ap`, minus the entropy term. -/

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C5v
end ItoLib

-- ===== CR =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5w
/-! CORE route, s28: finite-`h` lower bound for the plain chain from `q₀.2` on the PATH event
"ends in `A` and stays in `Bx`", in terms of the chain from `q₀.1` ending in `B` (`B` sits `ε` inside
`A`; `Bx` contains the `2δ`-neighbourhood of the segment from `q₀.1.2` to `q₀.2.2`). -/

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C5w
end ItoLib

-- ===== CJ =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5b
/-! CORE route C5b (s25): two Euler chains whose coefficients agree on a set `N` coincide as long
as one of them stays in `N` (used to replace the ball-localised coefficients of
`euler_close_tendsto` by the nondegenerate `σ ∘ π_N` of the steering). -/

variable {d : ℕ}

end C5b

end ItoLib

-- ===== CS =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5x
/-! CORE route, s28: transfer of `steer_lower_box` (stated for the box coefficients `s₂, b₂`)
to coefficients `s₁, b₁` that agree with `s₂, b₂` on the box `N`. -/

variable {d : ℕ}

variable {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C5x
end ItoLib

-- ===== CT =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5y
/-! CORE route, s28 (C5e): the `h → 0` limit. The chains of `steer_lower_s1` are compared with the
SDE solutions through `euler_close_tendsto`; the result is a minorisation of `P(X^y_T ∈ F)` by
`P(X^x_T ∈ F_{4ρ})` (`F_r = {z | ball z r ⊆ F}`) up to explicit errors that are small for small `T`. -/

variable {d : ℕ}

end C5y
end ItoLib

-- ===== CU =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5z
/-! CORE route, s28 (C5f, first half): `ρ → 0` in `core_minor` turns `F_{4ρ}` into `interior F`. -/

variable {d : ℕ}

end C5z
end ItoLib

-- ===== CV =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5fa
/-! CORE route, s29 (C5f-a): `R → ∞` in `core_minor_int` with a truncation family `s₁ R, b₁ R`. -/

variable {d : ℕ}

end C5fa
end ItoLib

-- ===== CA =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CA (CORE route, s22): measure-theoretic transfer lemmas for the Euler-limit minorization.
A lower bound `c L(int F) ≤ μ F + η` on closed sets (what a weak/in-probability limit gives)
upgrades to all Borel sets, and a common lower bound of two probability measures bounds their
total variation distance. -/

end ItoLib

-- ===== CW =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5fb
/-! CORE route, s29 (C5f-b): the closed-set minorisation of `core_minor_lim` gives a TV overlap
of the two time-`T` laws. -/

variable {d : ℕ}

end C5fb
end ItoLib

-- ===== CX =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5g
/-! CORE route, s29 (C5g): instantiation for the Kolmogorov model. For a box `[α, β]ⁿ` with
`α > 0` and every small `T > 0`, the time-`T` laws from any two points of the box overlap. -/

open StochKolmogorov.Persist

variable {n : ℕ}

end C5g
end ItoLib

-- ===== QA =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QA
/-! lemma_3_1 (aaf23e78) toolkit, part QA: continuous versions of Ito integrals.
Dyadic grid `gpt m l = l / 2^m`, the horizon-free step integral `stepM` (mesh `2^{-q}` on
`[0,q]`), its values at finer grid points, and a continuous-time maximal inequality for
differences of step integrals (via `gmart_max`). -/

end QA
end ItoLib

-- ===== QB =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QB
/-! lemma_3_1 toolkit, part QB: uniform `L²`-continuity of a bounded continuous integrand, and
the pathwise identification of `stepM q t` as the limit of `t`-grid Riemann sums whose
coefficients are the level-`q` left values (grid comparison, step 1). -/

end QB
end ItoLib

-- ===== QC =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QC
/-! lemma_3_1 toolkit, part QC: grid comparison in `L²` and `stepM q t → J t` in probability
for every fixed `t` (bounded continuous adapted integrand). -/

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

end QC
end ItoLib

-- ===== QD =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QDan
/-! Pure analysis: a sequence of continuous functions with geometrically small successive
differences on growing intervals converges pointwise to a continuous limit. -/

end QDan

section QD

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

end QD

end ItoLib

-- ===== QE =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QEneg
variable {Ω : Type*} [MeasurableSpace Ω]

end QEneg

section QEF

end QEF

section QEface
open StochKolmogorov.Persist
variable {n : ℕ}

end QEface

end ItoLib

-- ===== QF =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QFgen
/-! Generic test function `F(x,y,a) = e^{-a} G(y)` along `(X, Y, A)`. -/
variable {d : ℕ}

end QFgen

section QFsat
/-! The concave saturation `h_m(u) = ∫₀ᵘ (1 - st(s - m)) ds`. -/

end QFsat

section QFell
/-! The logarithm `ℓ = log(1 + cᵀy) - Σ pᵢ log yᵢ` of `V`, its line derivatives, and bounds. -/
variable {n : ℕ}
open StochKolmogorov.Persist

end QFell

section QFalg
variable {n : ℕ}
open StochKolmogorov.Persist

end QFalg

section QFgenL
variable {n : ℕ}
open StochKolmogorov.Persist

end QFgenL

end ItoLib

-- ===== QG =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
open StochKolmogorov.Persist

section QG
/-! Clause 4b (3.6) of Lemma 3.1: `E V^δ₀(X_t) ≤ e^{δ₀ H t} V^δ₀(x)`. -/
variable {n : ℕ}

end QG

end ItoLib

-- ===== QH =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QH
/-! Clause 1 toolkit (E1): the Ito isometry as an upper bound, `E J_t² ≤ E ∫₀ᵗ H²`. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QH

end ItoLib

-- ===== QI =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QI
/-! Clause 1 toolkit (E3): weak maximal inequality for continuous versions of Ito integrals. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QI
end ItoLib

-- ===== QJ =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QJan
/-! Clause 1 toolkit (E4, part 1): analysis helpers. -/

end QJan

section QJ
/-! Clause 1 toolkit (E4, part 1): the continuous Ito integral as a function, and the Picard map. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QJ
end ItoLib

-- ===== QK =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QKan

end QKan

section QK
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QK
end ItoLib

-- ===== QL =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QL
/-! Clause 1 toolkit (E4, part 3): initial bound and the Picard moment bound. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QL
end ItoLib

-- ===== QM =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QM
/-! Clause 1 toolkit (E4, part 4): Borel–Cantelli for the Picard iterates. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QM
end ItoLib

-- ===== QN =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Nat
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QN
/-! Clause 1 toolkit (E4, part 5): almost-sure geometric convergence of the Picard iterates. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QN
end ItoLib

-- ===== QO =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QO
/-! Clause 1 toolkit (E4, part 6): the Picard limit process. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QO
end ItoLib

-- ===== QP =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QP
/-! Clause 1 toolkit (E4, part 7): the Picard limit solves the SDE (bounded Lipschitz case). -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QP
end ItoLib

-- ===== QZ4 =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QZ4
/-! Clause 1 toolkit (E4, final): strong existence for bounded globally Lipschitz coefficients. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QZ4
end ItoLib

-- ===== E5A =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E5A
/-! Clause 1 toolkit (E5, part 1): two solutions from the same point, of SDEs whose bounded
coefficients agree on a ball, coincide as long as the first stays in a smaller ball. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end E5A

end ItoLib

-- ===== E5B =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E5B
/-! Clause 1 toolkit (E5, part 2): gluing a consistent, non-exploding family of truncated
solutions into a global strong solution. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end E5B

end ItoLib

-- ===== HB =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! HB (Harris route, s30): iterates of a Markov kernel, drift iteration, and the TV-Cauchy
estimate for `kpow κ k x` coming from `hm_iterate` (HA). -/

section HB
variable {X : Type*} [MeasurableSpace X]

end HB
end ItoLib

-- ===== F41e =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41e
/-! F41e (eq_4_1 work, 986b9ae0, 2026-10-30): generic tools for the face overlap (E3):
integrand congruence, constant integrands, masked vectors, the face projection. -/

variable {n : ℕ}
open StochKolmogorov.Persist

end F41e
end ItoLib

-- ===== F41f =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41f
/-! F41f (eq_4_1 work, 986b9ae0, 2026-10-30): the lift of a face solution to a nondegenerate
`n`-dimensional SDE (additive noise in the coordinates off the face) and the face overlap. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end F41f
end ItoLib

-- ===== F41g =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41g
/-! F41g (eq_4_1 work, 986b9ae0, 2026-10-30): the face overlap property (E3) through the lifted
nondegenerate SDE and `core_tv`, and eq_4_1 without extra hypotheses. -/
open StochKolmogorov.Persist
variable {n : ℕ}

theorem face_overlap {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hpd : ∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef)
    (I : Finset (Fin n)) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ faceBox I α β, ∀ y ∈ faceBox I α β,
      MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε := by
  obtain ⟨T, ε, hε, h⟩ :=
    StochKolmogorov.Persist.kolmogorov_face_box_tv_overlap P C B X hX hC hpd I hα hαβ
  exact ⟨T, ε, hε, fun x hx y hy => h x hx.1 hx.2 y hy.1 hy.2⟩
/-- (4.1) without the face-overlap hypothesis. -/
theorem eq_4_1_full (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h12 : Assumption12 P C X) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ p ∈ openOrthant n, l1 p = δ₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ IsWeightedInvasionMin P C X p ρ :=
  eq_4_1_of_face_overlap hn P C B X hX c γb hA h12 δ₀ hδ₀
    (fun I _ α β hα hαβ => face_overlap P C B X hX hA.2.1 hA.1 I hα hαβ)

end F41g
end ItoLib

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators in
open StochKolmogorov.Persist in
open EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h12 : Assumption12 P C X) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ p ∈ openOrthant n, l1 p = δ₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧
      IsWeightedInvasionMin P C X p ρ := by
  exact ItoLib.eq_4_1_full hn P C B X hX c γb hA h12 δ₀ hδ₀
