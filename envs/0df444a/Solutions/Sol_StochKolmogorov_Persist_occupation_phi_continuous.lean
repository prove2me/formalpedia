-- Prove2me | solution 1 for StochKolmogorov.Persist.occupation_phi_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-01T01:59:46.921378+00:00
-- url     : https://prove2.me/submissions/5175e1a8-fc52-4ebb-bf11-ea0d3504889e

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence

set_option linter.all false


-- ===== ItoM1 =====
section FlatM_ItoM1

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

end FlatM_ItoM1
-- ===== E =====
section FlatM_E
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

end FlatM_E
-- ===== F =====
section FlatM_F
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

end FlatM_F
-- ===== G =====
section FlatM_G
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


section M10c6
/-! M10c-6: pathwise error of the truncated Euler scheme: on `[0, T]` the coefficient errors
`s₁(Y_u) - H_u`, `b₁(Y_u) - b_u` are `O(osc_w(h) + h)` (lag start `a = y`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c6

end ItoLib

end FlatM_G
-- ===== H =====
section FlatM_H
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

end FlatM_H
-- ===== I =====
section FlatM_I
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

end FlatM_I
-- ===== J =====
section FlatM_J
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

end FlatM_J
-- ===== K =====
section FlatM_K
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

end FlatM_K
-- ===== L =====
section FlatM_L
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

end FlatM_L
-- ===== CB =====
section FlatM_CB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CB (CORE route C2, s22): Cameron-Martin shift formula for centered Gaussians, one-dimensional
and for finite independent families (`Measure.pi`). -/

end ItoLib

end FlatM_CB
-- ===== CC =====
section FlatM_CC
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

end FlatM_CC
-- ===== CD =====
section FlatM_CD
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

end FlatM_CD
-- ===== CE =====
section FlatM_CE
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

end FlatM_CE
-- ===== CF =====
section FlatM_CF
open Filter Set
open scoped BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CORE route C4b (s23): the steered second-moment recursion. If
`e_{k+1} ≤ (1 - 1/(m-k))² e_k + c h (e_k + e_{k-1})` (with `e_{-1}` given by `e' 0`), then
`e_k ≤ G ((m-k)/m)² (1 + 13 c h)^k` for `k < m`. Key fact: `(j+1)² + (j+2)² ≤ 13 j²` for `j ≥ 1`. -/

end ItoLib

end FlatM_CF
-- ===== CG =====
section FlatM_CG
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

end FlatM_CG
-- ===== CH =====
section FlatM_CH
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

end FlatM_CH
-- ===== CI =====
section FlatM_CI
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

end FlatM_CI
-- ===== CK =====
section FlatM_CK
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

end FlatM_CK
-- ===== CL =====
section FlatM_CL
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

end FlatM_CL
-- ===== M =====
section FlatM_M
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

end FlatM_M
-- ===== N =====
section FlatM_N
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

end FlatM_N
-- ===== O =====
section FlatM_O
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

end FlatM_O
-- ===== P =====
section FlatM_P
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10h
/-! M10h (b9/b11): local Lipschitz on compact sets, coordinate clamps, truncation families,
and the Kolmogorov coefficients. -/

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

end FlatM_P
-- ===== CM =====
section FlatM_CM
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

end FlatM_CM
-- ===== CN =====
section FlatM_CN
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

end FlatM_CN
-- ===== QA =====
section FlatM_QA
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

end FlatM_QA
-- ===== QB =====
section FlatM_QB
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

end FlatM_QB
-- ===== QC =====
section FlatM_QC
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

end FlatM_QC
-- ===== QD =====
section FlatM_QD
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

end FlatM_QD
-- ===== Q =====
section FlatM_Q
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

end FlatM_Q
-- ===== R =====
section FlatM_R
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

end FlatM_R
-- ===== S =====
section FlatM_S
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

end FlatM_S
-- ===== U =====
section FlatM_U
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

end FlatM_U
-- ===== QE =====
section FlatM_QE
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

end FlatM_QE
-- ===== QF =====
section FlatM_QF
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

noncomputable def Sf (c y : SDEState n) : ℝ := 1 + ∑ i, c i * y i
theorem one_le_Sf {c y : SDEState n} (hc : c ∈ openOrthant n) (hy : y ∈ orthant n) :
    1 ≤ Sf c y := by
  unfold Sf
  have : 0 ≤ ∑ i, c i * y i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hy i)
  linarith

theorem coord_le_Sf {c y : SDEState n} (hc : c ∈ openOrthant n) (hy : y ∈ orthant n) (i : Fin n) :
    c i * y i ≤ Sf c y := by
  unfold Sf
  have := Finset.single_le_sum (f := fun j => c j * y j)
    (fun j _ => mul_nonneg (hc j).le (hy j)) (Finset.mem_univ i)
  simp only at this; linarith

end QFell

section QFalg
variable {n : ℕ}
open StochKolmogorov.Persist

theorem quad_sig (Γ : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ∑ j, (∑ i, v i * Γ j i) ^ 2 = ∑ i, ∑ i', v i * v i' * (Γ.transpose * Γ) i i' := by
  simp_rw [sq, Finset.sum_mul_sum, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j _ => ?_
  try ring

/-- `cBracket` in terms of `aᵢ = cᵢ zᵢ / S`. -/
theorem cBracket_form (C : Coeffs n) {c z : SDEState n} (hc : c ∈ openOrthant n)
    (hz : z ∈ orthant n) :
    cBracket C c z = ∑ i, c i * z i / Sf c z * C.f i z -
      (1 / 2) * ∑ i, ∑ i', (c i * z i / Sf c z * C.g i z) * (c i' * z i' / Sf c z * C.g i' z) *
        C.sig i i' := by
  have hS : Sf c z ≠ 0 := by linarith [one_le_Sf hc hz]
  unfold cBracket
  have e1 : (∑ i, c i * z i * C.f i z) / (1 + ∑ i, c i * z i) =
      ∑ i, c i * z i / Sf c z * C.f i z := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by unfold Sf at hS ⊢; field_simp
  have e2 : (∑ i, ∑ j, C.sig i j * c i * c j * z i * z j * C.g i z * C.g j z) /
      (1 + ∑ i, c i * z i) ^ 2 = ∑ i, ∑ i', (c i * z i / Sf c z * C.g i z) *
        (c i' * z i' / Sf c z * C.g i' z) * C.sig i i' := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by unfold Sf at hS ⊢; field_simp
  rw [e1, mul_div_assoc, e2]
  try ring

theorem a_mem {c z : SDEState n} (hc : c ∈ openOrthant n) (hz : z ∈ orthant n) (i : Fin n) :
    0 ≤ c i * z i / Sf c z ∧ c i * z i / Sf c z ≤ 1 := by
  have hS := one_le_Sf hc hz
  refine ⟨div_nonneg (mul_nonneg (hc i).le (hz i)) (by linarith), ?_⟩
  rw [div_le_one (by linarith)]
  exact coord_le_Sf hc hz i

theorem dsum_le (u : Fin n → ℝ) (sig : Fin n → Fin n → ℝ) (i : Fin n) :
    |u i * u i * sig i i| ≤ ∑ i', |u i * u i' * sig i i'| :=
  Finset.single_le_sum (f := fun i' => |u i * u i' * sig i i'|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ i)

/-- Lower bound of the bracket used for `δ₀ < 1`. -/
theorem cBracket_ge (C : Coeffs n) {c z : SDEState n} (hc : c ∈ openOrthant n)
    (hz : z ∈ orthant n) :
    -(∑ i, |C.f i z|) - (1 / 2) * ∑ i, ∑ i', |C.g i z * C.g i' z * C.sig i i'| ≤ cBracket C c z := by
  rw [cBracket_form C hc hz]
  have h1 : -(∑ i, |C.f i z|) ≤ ∑ i, c i * z i / Sf c z * C.f i z := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h0, h1⟩ := a_mem hc hz i
    have : |c i * z i / Sf c z * C.f i z| ≤ |C.f i z| := by
      rw [abs_mul, abs_of_nonneg h0]; exact mul_le_of_le_one_left (abs_nonneg _) h1
    linarith [neg_abs_le (c i * z i / Sf c z * C.f i z)]
  have h2 : ∑ i, ∑ i', (c i * z i / Sf c z * C.g i z) * (c i' * z i' / Sf c z * C.g i' z) *
      C.sig i i' ≤ ∑ i, ∑ i', |C.g i z * C.g i' z * C.sig i i'| := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => ?_
    obtain ⟨a0, a1⟩ := a_mem hc hz i
    obtain ⟨b0, b1⟩ := a_mem hc hz i'
    have e : (c i * z i / Sf c z * C.g i z) * (c i' * z i' / Sf c z * C.g i' z) * C.sig i i' =
        (c i * z i / Sf c z * (c i' * z i' / Sf c z)) * (C.g i z * C.g i' z * C.sig i i') := by ring
    rw [e]
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_of_nonneg (mul_nonneg a0 b0)]
    exact mul_le_of_le_one_left (abs_nonneg _) (mul_le_one₀ a1 b0 b1)
  linarith

/-- `δ₀ < 1`, from Assumption 1.1 at a far point and (3.2). -/
theorem delta0_lt_one (hn : 0 < n) {C : Coeffs n} {c : SDEState n} {γb δ₀ : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) : δ₀ < 1 := by
  obtain ⟨-, -, hc, hγ, ε, hε, R, hR⟩ := hA
  obtain ⟨hδ0, hδγ, hδg⟩ := hδ
  by_contra h1
  push_neg at h1
  set i0 : Fin n := ⟨0, hn⟩
  set x : SDEState n := EuclideanSpace.single i0 (|R| + 1) with hx
  have hxo : x ∈ orthant n := fun j => by
    rw [hx, EuclideanSpace.single_apply]; split_ifs <;> positivity
  have hl : R ≤ l1 x := by
    unfold l1
    rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hx, EuclideanSpace.single_apply, hj])
      (by simp)]
    rw [show x i0 = |R| + 1 by simp [hx], abs_of_pos (by positivity)]
    linarith [le_abs_self R]
  have hA1 := hR x hxo hl
  have hD := hδg x hxo
  have hcb := cBracket_ge C hc hxo
  set F := ∑ i, |C.f i x|
  set T := ∑ i, ∑ i', |C.g i x * C.g i' x * C.sig i i'|
  set Gs := ∑ i, C.g i x ^ 2
  have hF : 0 ≤ F := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => abs_nonneg _
  have hG : 0 ≤ Gs := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsplit : ∑ i, (|C.f i x| + C.g i x ^ 2) = F + Gs := Finset.sum_add_distrib
  have hT' : 3 * δ₀ * T = 3 * δ₀ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| := rfl
  rw [hsplit] at hA1
  have hγ1 : 1 ≤ γb := by linarith
  have p1 : F ≤ γb * F := le_mul_of_one_le_left hF hγ1
  have p2 : T ≤ δ₀ * T := le_mul_of_one_le_left hT h1
  nlinarith

theorem p_le_l1 {p : SDEState n} (hp : p ∈ openOrthant n) (i : Fin n) : p i ≤ l1 p := by
  unfold l1
  have := Finset.single_le_sum (f := fun j => |p j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  simp only at this
  rwa [abs_of_pos (hp i)] at this

end QFalg

section QFgenL
variable {n : ℕ}
open StochKolmogorov.Persist

end QFgenL

end ItoLib

end FlatM_QF
-- ===== QG =====
section FlatM_QG
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

end FlatM_QG
-- ===== PA =====
section FlatM_PA
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace P41L
open ItoLib EthierKurtz StochKolmogorov.Persist

section Gen
/-! Generic saturation `G = hsat m ∘ φ` of a coercive `C²` function `φ` on the open orthant. -/
variable {n : ℕ}

variable {φ : SDEState n → ℝ} {m : ℝ} {K : Set (SDEState n)}

variable {φ1 φ2 : SDEState n → SDEState n → ℝ}

end Gen

section C1
/-! (4.11): `E V̂^δ₀(X_t) ≤ e^{δ₀Ht} V̂^δ₀(x)` via `φ_ε = U_δ₀(-p) + ε U_δ₀(p)`. -/
variable {n : ℕ}

end C1

end P41L

end FlatM_PA
-- ===== V =====
section FlatM_V
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

end FlatM_V
-- ===== W =====
section FlatM_W
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

end FlatM_W
-- ===== Y =====
section FlatM_Y
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

theorem posPart_of_mem {x : SDEState n} (hx : x ∈ orthant n) : posPart x = x := by
  ext i; rw [posPart_apply']; exact max_eq_left (hx i)

/-- The weight `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)`, read at `x⁺`. -/
noncomputable def wK (C : Coeffs n) (γb δ₀ : ℝ) (x : SDEState n) : ℝ :=
  γb + δ₀ * ∑ i, (|C.f i (posPart x)| + C.g i (posPart x) ^ 2)

end M12b

end ItoLib

end FlatM_Y
-- ===== PB =====
section FlatM_PB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace P41L
open ItoLib EthierKurtz StochKolmogorov.Persist

section C2a
/-! C2 ingredients: `ℓ = ln V + A`, its generator `Φ`, the cut-off drift bound `gm`. -/
variable {n : ℕ}

noncomputable def PhiT (C : Coeffs n) (c p y : SDEState n) : ℝ := Phi C c p (posPart y)

theorem PhiT_continuous (C : Coeffs n) {c : SDEState n} (p : SDEState n) (hc : c ∈ openOrthant n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Continuous (PhiT C c p) := by
  have hf : ∀ i, Continuous fun x => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hg : ∀ i, Continuous fun x => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hx : ∀ i, Continuous fun x : SDEState n => posPart x i := fun i =>
    (PiLp.continuous_apply 2 _ i).comp continuous_posPart
  have hS : Continuous fun x : SDEState n => 1 + ∑ i, c i * posPart x i :=
    continuous_const.add (continuous_finsetSum _ fun i _ => continuous_const.mul (hx i))
  have hS0 : ∀ x : SDEState n, 1 + ∑ i, c i * posPart x i ≠ 0 := fun x => by
    have := one_le_Sf hc (posPart_mem_orthant x); unfold Sf at this; linarith
  have h1 : Continuous fun x : SDEState n => (∑ i, c i * posPart x i * C.f i (posPart x)) /
      (1 + ∑ i, c i * posPart x i) :=
    (continuous_finsetSum _ fun i _ => (continuous_const.mul (hx i)).mul (hf i)).div hS hS0
  have h2 : Continuous fun x : SDEState n => (1 / 2) * (∑ i, ∑ j, C.sig i j * c i * c j *
      posPart x i * posPart x j * C.g i (posPart x) * C.g j (posPart x)) /
        (1 + ∑ i, c i * posPart x i) ^ 2 :=
    (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (((((continuous_const.mul continuous_const).mul continuous_const).mul (hx i)).mul
        (hx j)).mul (hg i)).mul (hg j))).div (hS.pow 2) fun x => pow_ne_zero 2 (hS0 x)
  have h3 : Continuous fun x : SDEState n => ∑ i, p i * (C.f i (posPart x) -
      C.sig i i * C.g i (posPart x) ^ 2 / 2) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul ((hf i).sub
      ((continuous_const.mul ((hg i).pow 2)).div_const 2))
  exact (h1.sub h2).sub h3

/-- `|Φ| ≤ K wK`. -/
theorem PhiT_abs_le (hn : 0 < n) {C : Coeffs n} {c p : SDEState n} {γb δ₀ : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) (y : SDEState n) :
    |PhiT C c p y| ≤ (2 / δ₀ + γb / (3 * δ₀ ^ 2)) * wK C γb δ₀ y := by
  have hc := hA.2.2.1
  have hγ := hA.2.2.2.1
  have hδ0 := hδ.1
  have hδ1 := delta0_lt_one hn hA hδ
  have hzo : posPart y ∈ orthant n := posPart_mem_orthant y
  have hpd : ∀ i, p i ≤ δ₀ := fun i => (p_le_l1 hp i).trans hpl
  set z := posPart y with hzdef
  set F := ∑ i, |C.f i z| with hF
  set T := ∑ i, ∑ i', |C.g i z * C.g i' z * C.sig i i'| with hT
  set G2 := ∑ i, C.g i z ^ 2 with hG2
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => abs_nonneg _
  have hG0 : 0 ≤ G2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcb_up : cBracket C c z ≤ F := by
    rw [cBracket_form C hc hzo]
    have h1 : ∑ i, c i * z i / Sf c z * C.f i z ≤ F := Finset.sum_le_sum fun i _ => by
      obtain ⟨h0, h1⟩ := a_mem hc hzo i
      have : |c i * z i / Sf c z * C.f i z| ≤ |C.f i z| := by
        rw [abs_mul, abs_of_nonneg h0]; exact mul_le_of_le_one_left (abs_nonneg _) h1
      exact (le_abs_self _).trans this
    have h2 : 0 ≤ ∑ i, ∑ i', (c i * z i / Sf c z * C.g i z) * (c i' * z i' / Sf c z * C.g i' z) *
        C.sig i i' := by
      have h0 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
        sq_nonneg (∑ i, (c i * z i / Sf c z * C.g i z) * C.Γ j i))
      rw [quad_sig] at h0
      exact h0
    linarith
  have hcb_lo := cBracket_ge C hc hzo
  have hdiag : ∑ i, |C.g i z * C.g i z * C.sig i i| ≤ T :=
    Finset.sum_le_sum fun i _ => dsum_le (fun i => C.g i z) C.sig i
  have hd : ∀ i, |p i * (C.f i z - C.sig i i * C.g i z ^ 2 / 2)| ≤
      δ₀ * (|C.f i z| + (1 / 2) * |C.g i z * C.g i z * C.sig i i|) := fun i => by
    rw [abs_mul, abs_of_pos (hp i)]
    have : |C.f i z - C.sig i i * C.g i z ^ 2 / 2| ≤
        |C.f i z| + (1 / 2) * |C.g i z * C.g i z * C.sig i i| := by
      have e : C.sig i i * C.g i z ^ 2 / 2 = (1 / 2) * (C.g i z * C.g i z * C.sig i i) := by ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul (hpd i) this (abs_nonneg _) hδ0.le
  have hPs : |∑ i, p i * (C.f i z - C.sig i i * C.g i z ^ 2 / 2)| ≤ δ₀ * (F + (1 / 2) * T) := by
    calc _ ≤ ∑ i, |p i * (C.f i z - C.sig i i * C.g i z ^ 2 / 2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, δ₀ * (|C.f i z| + (1 / 2) * |C.g i z * C.g i z * C.sig i i|) :=
          Finset.sum_le_sum fun i _ => hd i
      _ = δ₀ * (F + (1 / 2) * ∑ i, |C.g i z * C.g i z * C.sig i i|) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ δ₀ * (F + (1 / 2) * T) :=
          mul_le_mul_of_nonneg_left (by linarith) hδ0.le
  have hDel := hδ.2.2 z hzo
  have hTb : 3 * δ₀ * T ≤ γb * G2 := by
    have : 0 ≤ δ₀ * G2 := mul_nonneg hδ0.le hG0
    linarith
  have hw : wK C γb δ₀ y = γb + δ₀ * (F + G2) := by
    unfold wK; rw [Finset.sum_add_distrib]
  have hk : (2 / δ₀ + γb / (3 * δ₀ ^ 2)) * δ₀ = 2 + γb / (3 * δ₀) := by
    field_simp
  set Kc := 2 / δ₀ + γb / (3 * δ₀ ^ 2) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have hKw : (2 + γb / (3 * δ₀)) * (F + G2) ≤ Kc * wK C γb δ₀ y := by
    rw [hw]
    have : Kc * (γb + δ₀ * (F + G2)) = Kc * γb + (Kc * δ₀) * (F + G2) := by ring
    rw [this, hk]
    have := mul_nonneg hKc0 hγ.le
    linarith
  have hq : γb / (3 * δ₀) * (3 * δ₀ * T) = γb * T := by field_simp
  have hTb2 : T ≤ γb / (3 * δ₀) * G2 := by
    have h1 := mul_le_mul_of_nonneg_left hTb (by positivity : (0 : ℝ) ≤ γb / (3 * δ₀))
    have h2 : γb / (3 * δ₀) * (γb * G2) = γb * (γb / (3 * δ₀) * G2) := by ring
    rw [hq, h2] at h1
    exact le_of_mul_le_mul_left h1 hγ
  have hX : 0 ≤ γb / (3 * δ₀) * F := by positivity
  have hY : 0 ≤ 2 * G2 := by positivity
  have hδF : δ₀ * F ≤ F := mul_le_of_le_one_left hF0 hδ1.le
  have hδT : δ₀ * T ≤ T := mul_le_of_le_one_left hT0 hδ1.le
  have hPhi : PhiT C c p y = cBracket C c z - ∑ i, p i * (C.f i z - C.sig i i * C.g i z ^ 2 / 2) :=
    rfl
  rw [hPhi, abs_le]
  obtain ⟨hs1, hs2⟩ := abs_le.1 hPs
  constructor <;> nlinarith

end C2a

section C2b
variable {n : ℕ}

theorem path_cont {Ω : Type*} {Y : ℝ≥0 → Ω → SDEState n} (hc : ∀ ω, Continuous fun s => Y s ω)
    {h : SDEState n → ℝ} (hh : Continuous h) (ω : Ω) :
    Continuous (fun u : ℝ => h (Y u.toNNReal ω)) :=
  hh.comp ((hc ω).comp continuous_real_toNNReal)

end C2b

section C2c
variable {n : ℕ}

theorem occ_lint' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) (T : ℝ) (g : SDEState n → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂(occMean P X x T) =
      (ENNReal.ofReal T)⁻¹ * ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, g (X x s.toNNReal ω)) ∂P := by
  have hF : Measurable (fun q : ℝ × Ω => X x q.1.toNNReal q.2) :=
    measurable_uncurry_of_continuous_of_measurable (u := fun (s : ℝ) (ω : Ω) => X x s.toNNReal ω)
      (fun ω => (hc ω).comp continuous_real_toNNReal) (fun s => hm _)
  unfold occMean
  rw [lintegral_smul_measure, lintegral_map hg hF,
    lintegral_prod_symm (fun q : ℝ × Ω => g (X x q.1.toNNReal q.2)) ((hg.comp hF).aemeasurable),
    smul_eq_mul]

theorem occ_ae' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) (T : ℝ)
    (hinv : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n) :
    ∀ᵐ y ∂(occMean P X x T), y ∈ orthant n := by
  have hS : MeasurableSet (orthant n)ᶜ := orthant_isClosed.measurableSet.compl
  have := occ_lint' P X x hm hc T ((orthant n)ᶜ.indicator 1) (measurable_one.indicator hS)
  rw [lintegral_indicator_one hS] at this
  rw [ae_iff]
  change occMean P X x T (orthant n)ᶜ = 0
  rw [this]
  have h0 : (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (orthant n)ᶜ.indicator 1 (X x s.toNNReal ω)) =ᵐ[P] 0 := by
    filter_upwards [hinv] with ω hω
    simp [Set.indicator_apply, hω]
  rw [lintegral_congr_ae h0]
  simp

theorem setIcc_eq_interval {h : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) :
    ∫ s in Set.Icc (0 : ℝ) T, h s = ∫ u in (0 : ℝ)..T, h u := by
  rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]

end C2c

end P41L

end FlatM_PB
-- ===== PC =====
section FlatM_PC
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
set_option autoImplicit false

namespace P41L
open ItoLib EthierKurtz StochKolmogorov.Persist

section C3
/-! C3: continuity of `(x, T) ↦ T ∫ Φ d(occMean)` from the Feller property and the
uniform moment bound (3.8) (Lemma 3.2), by truncation of `Φ` and dominated convergence. -/
variable {n : ℕ}

/-- The weight of (3.8), read at `y⁺`. -/
noncomputable def w38T (C : Coeffs n) (y : SDEState n) : ℝ :=
  1 + ∑ i, (|C.f i (posPart y)| + |C.g i (posPart y)| ^ 2)

/-- `(1 + cᵀy⁺)^δ₀`. -/
noncomputable def rhoT (c : SDEState n) (δ₀ : ℝ) (y : SDEState n) : ℝ :=
  (1 + ∑ i, c i * posPart y i) ^ δ₀

theorem w38T_continuous (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Continuous (w38T C) := by
  have hf : ∀ i, Continuous fun x => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hg : ∀ i, Continuous fun x => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  exact continuous_const.add (continuous_finsetSum _ fun i _ => (hf i).abs.add ((hg i).abs.pow 2))

theorem w38T_nonneg (C : Coeffs n) (y : SDEState n) : 0 ≤ w38T C y := by
  unfold w38T
  have : 0 ≤ ∑ i, (|C.f i (posPart y)| + |C.g i (posPart y)| ^ 2) :=
    Finset.sum_nonneg fun i _ => by positivity
  linarith

theorem rhoT_continuous (c : SDEState n) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) : Continuous (rhoT c δ₀) := by
  have hx : ∀ i, Continuous fun x : SDEState n => posPart x i := fun i =>
    (PiLp.continuous_apply 2 _ i).comp continuous_posPart
  exact (Real.continuous_rpow_const hδ).comp
    (continuous_const.add (continuous_finsetSum _ fun i _ => continuous_const.mul (hx i)))

theorem one_le_rhoT {c : SDEState n} (hc : c ∈ openOrthant n) {δ₀ : ℝ} (hδ : 0 ≤ δ₀)
    (y : SDEState n) : 1 ≤ rhoT c δ₀ y := by
  unfold rhoT
  refine Real.one_le_rpow ?_ hδ
  have := one_le_Sf hc (posPart_mem_orthant y); unfold Sf at this; linarith

theorem mj_nonneg {c : SDEState n} (hc : c ∈ openOrthant n) {δ₀ : ℝ} (hδ : 0 ≤ δ₀)
    (C : Coeffs n) (y : SDEState n) : 0 ≤ rhoT c δ₀ y * w38T C y :=
  mul_nonneg (le_trans zero_le_one (one_le_rhoT hc hδ y)) (w38T_nonneg C y)

theorem PhiT_le_w38 (hn : 0 < n) {C : Coeffs n} {c p : SDEState n} {γb δ₀ : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) (y : SDEState n) :
    |PhiT C c p y| ≤ ((2 / δ₀ + γb / (3 * δ₀ ^ 2)) * max γb δ₀) * w38T C y := by
  have h1 := PhiT_abs_le hn hA hδ hp hpl y
  have hδ0 := hδ.1
  have hγ := hA.2.2.2.1
  have hK : 0 ≤ 2 / δ₀ + γb / (3 * δ₀ ^ 2) := by positivity
  have h2 : wK C γb δ₀ y ≤ max γb δ₀ * w38T C y := by
    unfold wK w38T
    have hs : 0 ≤ ∑ i, (|C.f i (posPart y)| + C.g i (posPart y) ^ 2) :=
      Finset.sum_nonneg fun i _ => by positivity
    have e : ∑ i, (|C.f i (posPart y)| + |C.g i (posPart y)| ^ 2) =
        ∑ i, (|C.f i (posPart y)| + C.g i (posPart y) ^ 2) := by simp [sq_abs]
    rw [e, mul_add, mul_one]
    have := le_max_left γb δ₀
    have := mul_le_mul_of_nonneg_right (le_max_right γb δ₀) hs
    linarith
  calc _ ≤ _ := h1
    _ ≤ (2 / δ₀ + γb / (3 * δ₀ ^ 2)) * (max γb δ₀ * w38T C y) := mul_le_mul_of_nonneg_left h2 hK
    _ = _ := by ring

theorem PhiT_le_mj (hn : 0 < n) {C : Coeffs n} {c p : SDEState n} {γb δ₀ : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) (y : SDEState n) :
    |PhiT C c p y| ≤ ((2 / δ₀ + γb / (3 * δ₀ ^ 2)) * max γb δ₀) * (rhoT c δ₀ y * w38T C y) := by
  have h1 := PhiT_le_w38 hn hA hδ hp hpl y
  have hδ0 := hδ.1
  have hγ := hA.2.2.2.1
  have hK : 0 ≤ (2 / δ₀ + γb / (3 * δ₀ ^ 2)) * max γb δ₀ :=
    mul_nonneg (by positivity) (le_trans hγ.le (le_max_left _ _))
  have h2 : w38T C y ≤ rhoT c δ₀ y * w38T C y := by
    have := one_le_rhoT hA.2.2.1 hδ0.le y
    have := w38T_nonneg C y
    nlinarith
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hK)

theorem clamp_sub_le {B v : ℝ} (hB : 0 ≤ B) : |v - max (-B) (min B v)| ≤ |v| := by
  rcases le_or_gt 0 v with hv | hv
  · have e : max (-B) (min B v) = min B v :=
      max_eq_right (by have := le_min hB hv; linarith)
    rw [e, abs_of_nonneg hv, abs_le]; constructor
    · have := min_le_right B v; linarith
    · have := le_min hB hv; linarith
  · have e : min B v = v := min_eq_right (by linarith)
    rw [e, abs_of_neg hv, abs_le]; constructor
    · have := max_le (by linarith : -B ≤ 0) hv.le; linarith
    · have := le_max_right (-B) v; linarith

theorem clamp_abs_le' {B v : ℝ} (hB : 0 ≤ B) : |max (-B) (min B v)| ≤ |v| := by
  rcases le_or_gt 0 v with hv | hv
  · have e : max (-B) (min B v) = min B v :=
      max_eq_right (by have := le_min hB hv; linarith)
    rw [e, abs_of_nonneg hv, abs_of_nonneg (le_min hB hv)]; exact min_le_right B v
  · have e : min B v = v := min_eq_right (by linarith)
    have h1 := max_le (by linarith : -B ≤ 0) hv.le
    have h2 := le_max_right (-B) v
    rw [e, abs_of_neg hv, abs_of_nonpos h1]; linarith

theorem clamp_abs_le {B v : ℝ} (hB : 0 ≤ B) : |max (-B) (min B v)| ≤ B :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clamp_eq {B v : ℝ} (h : |v| ≤ B) : max (-B) (min B v) = v := by
  rw [min_eq_right (abs_le.1 h).2, max_eq_right (abs_le.1 h).1]

theorem norm_le_sum_of_mem {y : SDEState n} (hy : y ∈ orthant n) : ‖y‖ ≤ ∑ i, y i := by
  rw [EuclideanSpace.norm_eq]
  have h0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ => hy i
  have e : ∑ i, ‖y i‖ ^ 2 = ∑ i, y i ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
  rw [e]
  calc Real.sqrt (∑ i, y i ^ 2) ≤ Real.sqrt ((∑ i, y i) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hy i)
    _ = ∑ i, y i := Real.sqrt_sq h0

/-- `T ∫ h d(occMean) = ∫₀ᵀ E h(X_u) du` for bounded continuous `h` (Fubini). -/
theorem occ_fub {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) {T : ℝ} (hT : 0 < T) {h : SDEState n → ℝ}
    (hh : Continuous h) {M : ℝ} (hM : ∀ y, |h y| ≤ M) :
    T * ∫ y, h y ∂(occMean P X x T) = ∫ u in (0 : ℝ)..T, ∫ ω, h (X x u.toNNReal ω) ∂P := by
  have hF : Measurable (fun q : ℝ × Ω => X x q.1.toNNReal q.2) :=
    measurable_uncurry_of_continuous_of_measurable (u := fun (s : ℝ) (ω : Ω) => X x s.toNNReal ω)
      (fun ω => (hc ω).comp continuous_real_toNNReal) (fun s => hm _)
  have hint : Integrable (fun q : ℝ × Ω => h (X x q.1.toNNReal q.2))
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) :=
    Integrable.of_bound (hh.measurable.comp hF).aestronglyMeasurable M
      (ae_of_all _ fun q => by rw [Real.norm_eq_abs]; exact hM _)
  unfold occMean
  rw [integral_smul_measure, integral_map hF.aemeasurable hh.aestronglyMeasurable,
    integral_prod _ hint, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hT.le,
    ← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
  exact setIcc_eq_interval hT.le

theorem m_cont {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) {h : SDEState n → ℝ}
    (hh : Continuous h) {M : ℝ} (hM : ∀ y, |h y| ≤ M) :
    Continuous fun u : ℝ => ∫ ω, h (X x u.toNNReal ω) ∂P :=
  continuous_of_dominated (bound := fun _ => M)
    (fun u => (hh.measurable.comp (hm _)).aestronglyMeasurable)
    (fun u => ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hM _) (integrable_const M)
    (ae_of_all _ fun ω => path_cont hc hh ω)

theorem m_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) {h : SDEState n → ℝ}
    {M : ℝ} (hM : ∀ y, |h y| ≤ M) (u : ℝ) : |∫ ω, h (X x u.toNNReal ω) ∂P| ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => h (X x u.toNNReal ω)) (C := M)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hM _)
  simpa [Real.norm_eq_abs] using this

/-- Continuity of `(x, T) ↦ ∫₀ᵀ E h(X^x_u) du` from the Feller property. -/
theorem Gcont {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hm : ∀ x ∈ orthant n, ∀ t, Measurable (X x t))
    (hc : ∀ x ∈ orthant n, ∀ ω, Continuous fun t => X x t ω) (h : SDEState n →ᵇ ℝ)
    (hfel : ∀ t : ℝ≥0, ContinuousOn (fun x => ∫ ω, h (X x t ω) ∂P) (orthant n)) :
    ContinuousOn (fun q : SDEState n × ℝ => ∫ u in (0 : ℝ)..q.2, ∫ ω, h (X q.1 u.toNNReal ω) ∂P)
      (orthant n ×ˢ Ioi 0) := by
  rintro ⟨x0, T0⟩ ⟨hx0, hT0⟩
  simp only [Set.mem_Ioi] at hx0 hT0
  set M := ‖h‖ with hMdef
  have hM : ∀ y, |h y| ≤ M := fun y => by
    have := h.norm_coe_le_norm y; rwa [Real.norm_eq_abs] at this
  set m : SDEState n → ℝ → ℝ := fun x u => ∫ ω, h (X x u.toNNReal ω) ∂P with hmdef
  have hmc : ∀ x ∈ orthant n, Continuous (m x) := fun x hx =>
    m_cont P X x (hm x hx) (hc x hx) h.continuous hM
  have hmb : ∀ x u, |m x u| ≤ M := fun x u => m_bound P X x hM u
  set S := orthant n ×ˢ Ioi (0 : ℝ)
  have hfst : Tendsto Prod.fst (𝓝[S] (x0, T0)) (𝓝[orthant n] x0) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun q hq => hq.1⟩
  have hsnd : Tendsto Prod.snd (𝓝[S] (x0, T0)) (𝓝 T0) :=
    (continuous_snd.tendsto _).mono_left nhdsWithin_le_nhds
  -- I x = ∫₀^{T0+1} |m x - m x0| → 0
  set I : SDEState n → ℝ := fun x => ∫ u in (0 : ℝ)..(T0 + 1), |m x u - m x0 u| with hIdef
  have hI : Tendsto I (𝓝[orthant n] x0) (𝓝 0) := by
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := 0) (b := T0 + 1) (l := 𝓝[orthant n] x0)
      (F := fun x u => |m x u - m x0 u|) (f := fun _ => (0 : ℝ)) (fun _ => 2 * M)
      (eventually_nhdsWithin_of_forall fun x hx =>
        (((hmc x hx).sub (hmc x0 hx0)).abs).aestronglyMeasurable)
      (Eventually.of_forall fun x => ae_of_all _ fun u _ => by
        rw [Real.norm_eq_abs, abs_abs]
        have := abs_sub (m x u) (m x0 u)
        have := hmb x u; have := hmb x0 u; linarith)
      intervalIntegrable_const
      (ae_of_all _ fun u _ => by
        have := ((hfel u.toNNReal x0 hx0).tendsto.sub
          (tendsto_const_nhds (x := m x0 u))).abs
        simpa [hmdef] using this)
    simpa using this
  have hE : Tendsto (fun q : SDEState n × ℝ => ∫ u in (0 : ℝ)..q.2, m x0 u) (𝓝[S] (x0, T0))
      (𝓝 (∫ u in (0 : ℝ)..T0, m x0 u)) :=
    ((intervalIntegral.continuous_primitive (fun a b => (hmc x0 hx0).intervalIntegrable a b)
      0).tendsto T0).comp hsnd
  have hD : Tendsto (fun q : SDEState n × ℝ => ∫ u in (0 : ℝ)..q.2, (m q.1 u - m x0 u))
      (𝓝[S] (x0, T0)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (hI.comp hfst)
    have hev : ∀ᶠ q in 𝓝[S] (x0, T0), q ∈ S ∧ q.2 < T0 + 1 :=
      eventually_mem_nhdsWithin.and (hsnd.eventually (gt_mem_nhds (by linarith)))
    filter_upwards [hev] with q hq
    obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hq
    simp only [Set.mem_Ioi] at hq2
    have hint : Continuous fun u => |m q.1 u - m x0 u| := ((hmc _ hq1).sub (hmc x0 hx0)).abs
    calc ‖∫ u in (0 : ℝ)..q.2, (m q.1 u - m x0 u)‖
        ≤ ∫ u in (0 : ℝ)..q.2, ‖m q.1 u - m x0 u‖ :=
          intervalIntegral.norm_integral_le_integral_norm hq2.le
      _ = ∫ u in (0 : ℝ)..q.2, |m q.1 u - m x0 u| := by simp only [Real.norm_eq_abs]
      _ ≤ ∫ u in (0 : ℝ)..(T0 + 1), |m q.1 u - m x0 u| :=
          intervalIntegral.integral_mono_interval le_rfl hq2.le hq3.le
            (ae_of_all _ fun u => abs_nonneg _) (hint.intervalIntegrable _ _)
      _ = (I ∘ Prod.fst) q := rfl
  have hsum := hD.add hE
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq1 : q.1 ∈ orthant n := hq.1
  rw [intervalIntegral.integral_sub ((hmc _ hq1).intervalIntegrable _ _)
    ((hmc x0 hx0).intervalIntegrable _ _)]
  ring

end C3

section C3main

set_option maxHeartbeats 1000000 in
/-- Child C3 (p. 18, (4.14)): continuity of `(x, T) ↦ T ∫ Φ d(occMean)` on `ℝⁿ₊ × (0, ∞)`,
from the Feller property and (3.8) of Lemma 3.2 and the invariance of `ℝⁿ₊`. -/
theorem c3_feller_phi {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n)
    (hpδ : l1 p ≤ δ₀)
    (hinv : ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n)
    (H₂ : ℝ) (hH₂ : 0 < H₂)
    (h38 : ∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
      ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal ((1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + |C.g i (X x s.toNNReal ω)| ^ 2)))) ∂P ≤
        ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t)))
    (hfel : ∀ (t : ℝ≥0) (h : SDEState n →ᵇ ℝ),
      ContinuousOn (fun x => ∫ ω, h (X x t ω) ∂P) (orthant n)) :
    ContinuousOn (fun q : SDEState n × ℝ => q.2 * ∫ y, Phi C c p y ∂(occMean P X q.1 q.2))
      (orthant n ×ˢ Ioi 0) := by
  obtain ⟨hP, hB, hsol⟩ := id hX
  have := hP
  have hC := hA.2.1
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hγ : 0 < γb := hA.2.2.2.1
  have hδ0 : 0 < δ₀ := hδ₀.1
  have hm : ∀ x ∈ orthant n, ∀ t, Measurable (X x t) := fun x hx => (hsol x hx).1
  have hpc : ∀ x ∈ orthant n, ∀ ω, Continuous fun t => X x t ω := fun x hx => (hsol x hx).2.1
  set S := orthant n ×ˢ Ioi (0 : ℝ) with hSdef
  set K1 : ℝ := (2 / δ₀ + γb / (3 * δ₀ ^ 2)) * max γb δ₀ with hK1def
  have hK1 : 0 ≤ K1 := mul_nonneg (by positivity) (le_trans hγ.le (le_max_left _ _))
  have hmjc : Continuous fun y => rhoT c δ₀ y * w38T C y :=
    (rhoT_continuous c hδ0.le).mul (w38T_continuous C hC)
  have hmj0 : ∀ y, 0 ≤ rhoT c δ₀ y * w38T C y := fun y => mj_nonneg hc hδ0.le C y
  have hPc := PhiT_continuous C p hc hC
  have hsx : ∀ x ∈ orthant n, 0 ≤ (1 + ∑ i, c i * x i) ^ δ₀ := fun x hx =>
    Real.rpow_nonneg (by have := one_le_Sf hc hx; unfold Sf at this; linarith) _
  -- the (3.8) bound on occupation measures
  have hlint : ∀ x ∈ orthant n, ∀ T : ℝ, 0 < T →
      ∫⁻ y, ENNReal.ofReal (rhoT c δ₀ y * w38T C y) ∂(occMean P X x T) ≤
        (ENNReal.ofReal T)⁻¹ * ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + T)) := by
    intro x hx T hT
    have hmeas : Measurable fun y => ENNReal.ofReal (rhoT c δ₀ y * w38T C y) :=
      ENNReal.measurable_ofReal.comp hmjc.measurable
    rw [occ_lint' P X x (hm x hx) (hpc x hx) T _ hmeas]
    refine mul_le_mul' le_rfl ?_
    have htv : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT.le
    have h1 := h38 x hx T.toNNReal (Real.toNNReal_pos.2 hT)
    rw [htv] at h1
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) h1
    filter_upwards [hinv x hx] with ω hω
    refine lintegral_congr fun s => ?_
    simp only [rhoT, w38T]
    rw [posPart_of_mem (hω s.toNNReal)]
  have hmjI : ∀ x ∈ orthant n, ∀ T : ℝ, 0 < T →
      Integrable (fun y => rhoT c δ₀ y * w38T C y) (occMean P X x T) := by
    intro x hx T hT
    refine ⟨hmjc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hmj0)).2 ?_⟩
    exact lt_of_le_of_lt (hlint x hx T hT) (ENNReal.mul_lt_top (ENNReal.inv_lt_top.2
      (ENNReal.ofReal_pos.2 hT)) ENNReal.ofReal_lt_top)
  have hTmj : ∀ x ∈ orthant n, ∀ T : ℝ, 0 < T →
      T * ∫ y, rhoT c δ₀ y * w38T C y ∂(occMean P X x T) ≤
        H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + T) := by
    intro x hx T hT
    have hA0 : 0 ≤ H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + T) :=
      mul_nonneg hH₂.le (add_nonneg (hsx x hx) hT.le)
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hmj0) hmjc.aestronglyMeasurable]
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2
      (ENNReal.ofReal_pos.2 hT).ne') ENNReal.ofReal_ne_top) (hlint x hx T hT)
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hT.le,
      ENNReal.toReal_ofReal hA0] at h1
    have := mul_le_mul_of_nonneg_left h1 hT.le
    rwa [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul] at this
  -- Phi = PhiT on the support of the occupation measures
  have hEq : EqOn (fun q : SDEState n × ℝ => q.2 * ∫ y, PhiT C c p y ∂(occMean P X q.1 q.2))
      (fun q : SDEState n × ℝ => q.2 * ∫ y, Phi C c p y ∂(occMean P X q.1 q.2)) S := by
    rintro ⟨x, T⟩ ⟨hx, hT⟩
    dsimp only
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [occ_ae' P X x (hm x hx) (hpc x hx) T (hinv x hx)] with y hy
    simp only [PhiT, posPart_of_mem hy]
  refine ContinuousOn.congr ?_ hEq.symm
  intro q0 hq0
  refine continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt hq0 fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  set A : SDEState n × ℝ → ℝ := fun q => (1 + ∑ i, c i * q.1 i) ^ δ₀ + q.2 with hAdef
  have hAc : Continuous A :=
    ((Real.continuous_rpow_const hδ0.le).comp (continuous_const.add (continuous_finsetSum _
      fun i _ => continuous_const.mul ((PiLp.continuous_apply 2 _ i).comp continuous_fst)))).add
      continuous_snd
  have ht : {q | A q < A q0 + 1} ∩ S ∈ 𝓝[S] q0 :=
    inter_mem (nhdsWithin_le_nhds (hAc.continuousAt.preimage_mem_nhds
      (Iio_mem_nhds (by linarith)))) self_mem_nhdsWithin
  -- the minimum of `c`
  set i0 : Fin n := ⟨0, hn⟩
  set cm : ℝ := Finset.univ.inf' ⟨i0, Finset.mem_univ _⟩ (fun i => c i) with hcmdef
  have hcm : 0 < cm := (Finset.lt_inf'_iff _).2 fun i _ => hc i
  have hcmle : ∀ i, cm ≤ c i := fun i => Finset.inf'_le (fun i => c i) (Finset.mem_univ i)
  have hLt : Tendsto (fun R : ℝ => (1 + cm * R) ^ δ₀) atTop atTop :=
    (tendsto_rpow_atTop hδ0).comp (tendsto_atTop_mono
      (fun R => show cm * R ≤ 1 + cm * R by linarith) (tendsto_id.const_mul_atTop hcm))
  obtain ⟨R, hRL, hR0⟩ := ((hLt.eventually_gt_atTop (K1 * H₂ * (A q0 + 1) / ε)).and
    (eventually_ge_atTop 0)).exists
  have hcR : 0 < 1 + cm * R := add_pos_of_pos_of_nonneg one_pos (mul_nonneg hcm.le hR0)
  set L := (1 + cm * R) ^ δ₀ with hLdef
  have hL : 0 < L := Real.rpow_pos_of_pos hcR _
  -- truncation of PhiT at a bound valid on the ball of radius R
  obtain ⟨Bd, hBd⟩ := (isCompact_closedBall (0 : SDEState n) R).exists_bound_of_continuousOn
    hPc.continuousOn
  set Bp := max Bd 0 with hBpdef
  have hBp : 0 ≤ Bp := le_max_right _ _
  set cl : SDEState n → ℝ := fun y => max (-Bp) (min Bp (PhiT C c p y)) with hcldef
  have hclc : Continuous cl := continuous_const.max (continuous_const.min hPc)
  have hclb : ∀ y, ‖cl y‖ ≤ Bp := fun y => by
    rw [Real.norm_eq_abs]; exact clamp_abs_le hBp
  set hR : SDEState n →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup cl hclc Bp hclb
  have hRe : ∀ y, hR y = cl y := fun y => rfl
  have hRb : ∀ y, |hR y| ≤ Bp := fun y => by rw [← Real.norm_eq_abs]; exact hclb y
  -- pointwise truncation error on the orthant
  have herr : ∀ y ∈ orthant n, |PhiT C c p y - hR y| ≤ K1 / L * (rhoT c δ₀ y * w38T C y) := by
    intro y hy
    rw [hRe]
    by_cases hyR : ‖y‖ ≤ R
    · have hb := hBd y (by rw [Metric.mem_closedBall, dist_zero_right]; exact hyR)
      rw [Real.norm_eq_abs] at hb
      have : cl y = PhiT C c p y := clamp_eq (hb.trans (le_max_left _ _))
      rw [this, sub_self, abs_zero]
      exact mul_nonneg (div_nonneg hK1 hL.le) (hmj0 y)
    · have hyR' := not_le.1 hyR
      have h1 := clamp_sub_le (v := PhiT C c p y) hBp
      have h2 := PhiT_le_w38 hn hA hδ₀ hp hpδ y
      have hρ : L ≤ rhoT c δ₀ y := by
        unfold rhoT
        rw [posPart_of_mem hy]
        refine Real.rpow_le_rpow hcR.le ?_ hδ0.le
        have hs := norm_le_sum_of_mem hy
        have h3 : cm * ∑ i, y i ≤ ∑ i, c i * y i := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcmle i) (hy i)
        have h4 := mul_le_mul_of_nonneg_left (hyR'.le.trans hs) hcm.le
        linarith
      have hw := w38T_nonneg C y
      calc |PhiT C c p y - cl y| ≤ |PhiT C c p y| := h1
        _ ≤ K1 * w38T C y := h2
        _ = K1 / L * (L * w38T C y) := by field_simp
        _ ≤ K1 / L * (rhoT c δ₀ y * w38T C y) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hρ hw) (div_nonneg hK1 hL.le)
  refine ⟨_, ht, fun q => q.2 * ∫ y, hR y ∂(occMean P X q.1 q.2), ?_, ?_⟩
  · -- continuity of the truncated functional
    have hG := Gcont P X hm hpc hR (fun t => hfel t hR)
    have hG' : ContinuousOn
        (fun q : SDEState n × ℝ => q.2 * ∫ y, hR y ∂(occMean P X q.1 q.2)) S := by
      refine hG.congr ?_
      rintro ⟨x, T⟩ ⟨hx, hT⟩
      exact occ_fub P X x (hm x hx) (hpc x hx) hT hR.continuous hRb
    exact hG' q0 hq0
  · rintro q ⟨hqA, hqS⟩
    apply hεu
    show dist (q.2 * ∫ y, PhiT C c p y ∂(occMean P X q.1 q.2))
      (q.2 * ∫ y, hR y ∂(occMean P X q.1 q.2)) < ε
    have hq1 : q.1 ∈ orthant n := hqS.1
    have hT : 0 < q.2 := hqS.2
    have hPI : Integrable (PhiT C c p) (occMean P X q.1 q.2) :=
      ((hmjI q.1 hq1 q.2 hT).const_mul K1).mono' hPc.aestronglyMeasurable
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact PhiT_le_mj hn hA hδ₀ hp hpδ y)
    have hRI : Integrable (fun y => hR y) (occMean P X q.1 q.2) :=
      ((hmjI q.1 hq1 q.2 hT).const_mul K1).mono' hR.continuous.aestronglyMeasurable
        (ae_of_all _ fun y => by
          rw [Real.norm_eq_abs, hRe]
          exact (clamp_abs_le' hBp).trans (PhiT_le_mj hn hA hδ₀ hp hpδ y))
    have hdiff : |∫ y, (PhiT C c p y - hR y) ∂(occMean P X q.1 q.2)| ≤
        ∫ y, K1 / L * (rhoT c δ₀ y * w38T C y) ∂(occMean P X q.1 q.2) := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hmjI q.1 hq1 q.2 hT).const_mul _) ?_
      filter_upwards [occ_ae' P X q.1 (hm q.1 hq1) (hpc q.1 hq1) q.2 (hinv q.1 hq1)]
        with y hy
      rw [Real.norm_eq_abs]; exact herr y hy
    rw [integral_sub hPI hRI, integral_const_mul] at hdiff
    have hTm := hTmj q.1 hq1 q.2 hT
    have hAq : A q < A q0 + 1 := hqA
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hT]
    calc q.2 * |∫ y, PhiT C c p y ∂(occMean P X q.1 q.2) - ∫ y, hR y ∂(occMean P X q.1 q.2)|
        ≤ q.2 * (K1 / L * ∫ y, rhoT c δ₀ y * w38T C y ∂(occMean P X q.1 q.2)) :=
          mul_le_mul_of_nonneg_left hdiff hT.le
      _ = K1 * (q.2 * ∫ y, rhoT c δ₀ y * w38T C y ∂(occMean P X q.1 q.2)) / L := by ring
      _ ≤ K1 * (H₂ * (A q0 + 1)) / L := by
          refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hK1) hL.le
          exact hTm.trans (mul_le_mul_of_nonneg_left hAq.le hH₂.le)
      _ < ε := by
          rw [div_lt_iff₀ hL]
          rw [div_lt_iff₀ hε] at hRL
          nlinarith

end C3main
end P41L

end FlatM_PC

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open StochKolmogorov.Persist in
open EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n)
    (hpδ : l1 p ≤ δ₀)
    (hinv : ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n)
    (H₂ : ℝ) (hH₂ : 0 < H₂)
    (h38 : ∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
      ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal ((1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + |C.g i (X x s.toNNReal ω)| ^ 2)))) ∂P ≤
        ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t)))
    (hfel : ∀ (t : ℝ≥0) (h : SDEState n →ᵇ ℝ),
      ContinuousOn (fun x => ∫ ω, h (X x t ω) ∂P) (orthant n)) :
    ContinuousOn (fun q : SDEState n × ℝ => q.2 * ∫ y, Phi C c p y ∂(occMean P X q.1 q.2))
      (orthant n ×ˢ Ioi 0) := by
  exact P41L.c3_feller_phi hn P C B X hX c γb hA δ₀ hδ₀ p hp hpδ hinv H₂ hH₂ h38 hfel
