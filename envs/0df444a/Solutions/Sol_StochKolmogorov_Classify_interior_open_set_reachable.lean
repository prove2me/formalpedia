-- Prove2me | solution 1 for StochKolmogorov.Classify.interior_open_set_reachable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T00:19:51.58996+00:00
-- url     : https://prove2.me/submissions/520ab9d9-1ef6-409b-b188-787de2f0d576

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
import Definitions.Def_StochKolmogorov_Classify_Model
import Theorems.Thm_EthierKurtz_brownian_sde_local_minorization
set_option linter.all false
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

/-- Every `u ∈ (0,t]` lies in a cell `(t_k, t_{k+1}]` of the dyadic grid, where the step process
takes the value `c k`. -/
theorem itoStepValue_eq_cell (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) {u : ℝ}
    (hu : u ∈ Set.Ioc 0 t.val) (ω : Ω) :
    ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n ∧
      itoStepValue t n c u ω = c k ω := by
  have ht : (0 : ℝ) < t.val := lt_of_lt_of_le hu.1 hu.2
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hx0 : 0 < u * 2 ^ n / t.val := by have := hu.1; positivity
  have hxle : u * 2 ^ n / t.val ≤ 2 ^ n := by
    rw [div_le_iff₀ ht]; nlinarith [hu.2]
  have hc1 : 0 < ⌈u * 2 ^ n / t.val⌉₊ := Nat.ceil_pos.2 hx0
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = ⌈u * 2 ^ n / t.val⌉₊ := ⟨⌈u * 2 ^ n / t.val⌉₊ - 1, by omega⟩
  have hkR : (k : ℝ) + 1 = ⌈u * 2 ^ n / t.val⌉₊ := by exact_mod_cast hk
  have hlt : (k : ℝ) < u * 2 ^ n / t.val := by
    have := Nat.ceil_lt_add_one hx0.le; linarith
  have hge : u * 2 ^ n / t.val ≤ (k : ℝ) + 1 := by rw [hkR]; exact Nat.le_ceil _
  have hk2 : k < 2 ^ n := by
    have : ⌈u * 2 ^ n / t.val⌉₊ ≤ 2 ^ n := Nat.ceil_le.2 (by exact_mod_cast hxle)
    omega
  have hlo : (k : ℝ) * t.val / 2 ^ n < u := by
    rw [div_lt_iff₀ h2]; rw [lt_div_iff₀ ht] at hlt; linarith
  have hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n := by
    rw [le_div_iff₀ h2]; rw [div_le_iff₀ ht] at hge; linarith
  refine ⟨k, hk2, hlo, hhi, ?_⟩
  unfold itoStepValue
  rw [Finset.sum_eq_single k]
  · rw [if_pos ⟨hlo, hhi⟩]
  · intro l _ hlk
    rw [if_neg]
    rintro ⟨h1, h1'⟩
    rcases lt_or_gt_of_ne hlk with hl | hl
    · have hl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast hl
      have : ((l : ℝ) + 1) * t.val / 2 ^ n ≤ (k : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith
  · intro hk'; exact absurd (Finset.mem_range.2 hk2) hk'

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

/-- The completed Brownian past does not depend on a constant initial condition. -/
theorem completedBrownianPast_const [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → SDEState d) (x y : SDEState d) :
    completedBrownianPast P W (fun _ => x) = completedBrownianPast P W (fun _ => y) := by
  funext t
  simp only [completedBrownianPast, MeasurableSpace.comap_const]

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

theorem state_norm_sq (x : SDEState d) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

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

/-- The compact pieces of an open face. -/
def faceBox (I : Finset (Fin n)) (α β : ℝ) : Set (SDEState n) :=
  {x | x ∈ faceOpen I ∧ ∀ i ∈ I, α ≤ x i ∧ x i ≤ β}

end F41c
end ItoLib

-- ===== X41 =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! X41 (eq_4_1, finite-`M` part): the minimax step of [SBA11, Lemma 4] for finitely many
boundary ergodic measures, by strict separation of a polytope from the closed negative orthant. -/

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

/-- Average diffusion matrix of a pair applied to `u`. -/
noncomputable def avgApply (p : SDEState d × SDEState d) (u : Fin d → ℝ) : SDEState d :=
  WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) + s₁ p.2 (i, j)) / 2 * u j)

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

/-- Right inverse of `avgApply s p` for `s x (i, j) = a i x * Γ j i`. -/
noncomputable def jInv (a : Fin d → SDEState d → ℝ) (Γ : Matrix (Fin d) (Fin d) ℝ)
    (p : SDEState d × SDEState d) (v : SDEState d) : Fin d → ℝ :=
  (Γ.transpose)⁻¹.mulVec (fun i => 2 * v i / (a i p.1 + a i p.2))

theorem jInv_right {s : SDEState d → SDEDiffusion d} {a : Fin d → SDEState d → ℝ}
    {Γ : Matrix (Fin d) (Fin d) ℝ} (hsa : ∀ x i j, s x (i, j) = a i x * Γ j i)
    (hΓ : IsUnit Γ.det) (ha : ∀ i x y, a i x + a i y ≠ 0) (p : SDEState d × SDEState d)
    (v : SDEState d) : avgApply s p (jInv a Γ p v) = v := by
  ext i
  have hT : Γ.transpose.mulVec (jInv a Γ p v) = fun i => 2 * v i / (a i p.1 + a i p.2) := by
    unfold jInv
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose]),
      Matrix.one_mulVec]
  have e : ∑ j, (s p.1 (i, j) + s p.2 (i, j)) / 2 * jInv a Γ p v j =
      (a i p.1 + a i p.2) / 2 * (Γ.transpose.mulVec (jInv a Γ p v)) i := by
    simp only [hsa, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∑ j, (s p.1 (i, j) + s p.2 (i, j)) / 2 * jInv a Γ p v j = v i
  rw [e, hT]
  have := ha i p.1 p.2
  field_simp

theorem jInv_measurable {a : Fin d → SDEState d → ℝ} (Γ : Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i, Measurable (a i)) : Measurable (Function.uncurry (jInv a Γ)) := by
  refine measurable_pi_lambda _ fun k => ?_
  simp only [Function.uncurry, jInv, Matrix.mulVec, dotProduct]
  refine Finset.measurable_sum _ fun i _ => measurable_const.mul ?_
  exact (measurable_const.mul ((EuclideanSpace.proj i).continuous.measurable.comp
    measurable_snd)).div (((ha i).comp (measurable_fst.comp measurable_fst)).add
      ((ha i).comp (measurable_snd.comp measurable_fst)))

theorem jInv_bound {a : Fin d → SDEState d → ℝ} (Γ : Matrix (Fin d) (Fin d) ℝ) {κ : ℝ}
    (hκ : 0 < κ) (ha : ∀ i x y, κ ≤ |a i x + a i y|) (p : SDEState d × SDEState d)
    (v : SDEState d) :
    ∑ j, jInv a Γ p v j ^ 2 ≤
      (2 * Real.sqrt (∑ j, ∑ k, (Γ.transpose)⁻¹ j k ^ 2) / κ) ^ 2 * ‖v‖ ^ 2 := by
  set M := (Γ.transpose)⁻¹ with hM
  set w : Fin d → ℝ := fun i => 2 * v i / (a i p.1 + a i p.2) with hw
  have hJ : ∀ j, jInv a Γ p v j = ∑ k, M j k * w k := fun j => rfl
  have hw2 : ∀ k, w k ^ 2 ≤ 4 / κ ^ 2 * v k ^ 2 := fun k => by
    have h1 : κ ^ 2 ≤ (a k p.1 + a k p.2) ^ 2 := by
      have := pow_le_pow_left₀ hκ.le (ha k p.1 p.2) 2
      rwa [sq_abs] at this
    have hκ2 : 0 < κ ^ 2 := by positivity
    rw [hw]
    simp only
    rw [div_pow, mul_pow, div_mul_eq_mul_div]
    norm_num
    exact div_le_div_of_nonneg_left (by positivity) hκ2 h1
  have hW : ∑ k, w k ^ 2 ≤ 4 / κ ^ 2 * ‖v‖ ^ 2 := by
    rw [state_norm_sq, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hw2 k
  simp_rw [hJ]
  calc ∑ j, (∑ k, M j k * w k) ^ 2 ≤ ∑ j, ((∑ k, M j k ^ 2) * ∑ k, w k ^ 2) :=
        Finset.sum_le_sum fun j _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ j, ∑ k, M j k ^ 2) * ∑ k, w k ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ k, M j k ^ 2) * (4 / κ ^ 2 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hW (Finset.sum_nonneg fun j _ =>
          Finset.sum_nonneg fun k _ => sq_nonneg _)
    _ = (2 * Real.sqrt (∑ j, ∑ k, M j k ^ 2) / κ) ^ 2 * ‖v‖ ^ 2 := by
        have hT0 : (0 : ℝ) ≤ ∑ j, ∑ k, M j k ^ 2 :=
          Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _
        rw [div_pow, mul_pow, Real.sq_sqrt hT0]
        ring

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

/-- Coordinatewise clamp to the box `[α, β]^n`. -/
noncomputable def boxP (α β : ℝ) (x : SDEState n) : SDEState n :=
  WithLp.toLp 2 (fun i => max α (min β (x i)))

theorem boxP_apply (α β : ℝ) (x : SDEState n) (i : Fin n) :
    boxP α β x i = max α (min β (x i)) := rfl

theorem box1_lip (α β a b : ℝ) : |max α (min β a) - max α (min β b)| ≤ |a - b| := by
  rw [abs_le]
  have h1 := le_abs_self (a - b); have h2 := neg_abs_le (a - b)
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

theorem boxP_lip (α β : ℝ) (x y : SDEState n) : ‖boxP α β x - boxP α β y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by rw [boxP_apply, boxP_apply]; exact box1_lip _ _ _ _

theorem boxP_mem {α β : ℝ} (hαβ : α ≤ β) (x : SDEState n) (i : Fin n) :
    α ≤ boxP α β x i ∧ boxP α β x i ≤ β := by
  rw [boxP_apply]
  exact ⟨le_max_left _ _, max_le hαβ (min_le_left _ _)⟩

theorem boxP_eq {α β : ℝ} {x : SDEState n} (hx : ∀ i, α ≤ x i ∧ x i ≤ β) : boxP α β x = x := by
  ext i
  rw [boxP_apply, min_eq_right (hx i).2, max_eq_right (hx i).1]

theorem boxP_continuous (α β : ℝ) : Continuous (boxP (n := n) α β) :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]; exact boxP_lip α β x y)

/-- Entrywise Lipschitz functions read through a bounded 1-Lipschitz map are globally Lipschitz
and bounded as vectors. -/
theorem boxed_vec_lip {ι : Type*} [Fintype ι] (φ : ι → SDEState n → ℝ) {β : ℝ}
    (hφ : ∀ k, ∃ L, 0 ≤ L ∧ ∀ u v : SDEState n, (∀ l, |u l| ≤ β) → (∀ l, |v l| ≤ β) →
      |φ k u - φ k v| ≤ L * ‖u - v‖)
    (π : SDEState n → SDEState n) (hπ : ∀ x l, |π x l| ≤ β)
    (hπL : ∀ x y, ‖π x - π y‖ ≤ ‖x - y‖) :
    ∃ L S : ℝ, 0 ≤ L ∧ ∀ x y : SDEState n,
      ‖(WithLp.toLp 2 (fun k => φ k (π x)) : EuclideanSpace ℝ ι) -
        WithLp.toLp 2 (fun k => φ k (π y))‖ ≤ L * ‖x - y‖ ∧
      ‖(WithLp.toLp 2 (fun k => φ k (π x)) : EuclideanSpace ℝ ι)‖ ≤ S := by
  choose L hL0 hL using hφ
  refine ⟨∑ k, L k, ∑ k, (L k * (n * (2 * β)) + |φ k (π 0)|),
    Finset.sum_nonneg fun k _ => hL0 k, fun x y => ⟨?_, ?_⟩⟩
  · calc _ ≤ ∑ k, |((WithLp.toLp 2 (fun k => φ k (π x)) : EuclideanSpace ℝ ι) -
          WithLp.toLp 2 (fun k => φ k (π y))) k| := euc_norm_le_sum' _
      _ ≤ ∑ k, L k * ‖x - y‖ := Finset.sum_le_sum fun k _ => by
          simp only [PiLp.sub_apply, PiLp.toLp_apply]
          exact (hL k _ _ (hπ x) (hπ y)).trans (mul_le_mul_of_nonneg_left (hπL x y) (hL0 k))
      _ = (∑ k, L k) * ‖x - y‖ := by rw [Finset.sum_mul]
  · calc _ ≤ ∑ k, |(WithLp.toLp 2 (fun k => φ k (π x)) : EuclideanSpace ℝ ι) k| :=
          euc_norm_le_sum' _
      _ ≤ ∑ k, (L k * (n * (2 * β)) + |φ k (π 0)|) := Finset.sum_le_sum fun k _ => by
          simp only [PiLp.toLp_apply]
          have h1 := hL k _ _ (hπ x) (hπ 0)
          have h2 : ‖π x - π 0‖ ≤ n * (2 * β) := norm_le_card_mul fun l => by
            rw [PiLp.sub_apply]
            have := abs_sub (π x l) (π 0 l)
            linarith [hπ x l, hπ 0 l]
          have h3 := abs_sub_abs_le_abs_sub (φ k (π x)) (φ k (π 0))
          nlinarith [mul_le_mul_of_nonneg_left h2 (hL0 k)]

open StochKolmogorov.Persist

/-- The diagonal factor of the boxed diffusion. -/
noncomputable def aK (C : Coeffs n) (α β : ℝ) (i : Fin n) (x : SDEState n) : ℝ :=
  boxP α β x i * C.g i (posPart (boxP α β x))

/-- Boxed Kolmogorov diffusion and drift. -/
noncomputable def sK (C : Coeffs n) (α β : ℝ) (x : SDEState n) : SDEDiffusion n :=
  diffusion C (0, boxP α β x)

noncomputable def bK (C : Coeffs n) (α β : ℝ) (x : SDEState n) : SDEState n :=
  drift C (0, boxP α β x)

theorem sK_apply (C : Coeffs n) (α β : ℝ) (x : SDEState n) (i j : Fin n) :
    sK C α β x (i, j) = aK C α β i x * C.Γ j i := rfl

theorem kolm_box (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    Continuous (sK C α β) ∧ Continuous (bK C α β) ∧ ∃ S L : ℝ, 0 ≤ L ∧
      (∀ x, ‖sK C α β x‖ ≤ S ∧ ‖bK C α β x‖ ≤ S) ∧
      (∀ x y, ‖sK C α β x - sK C α β y‖ ≤ L * ‖x - y‖ ∧
        ‖bK C α β x - bK C α β y‖ ≤ L * ‖x - y‖) := by
  have hβ : 0 ≤ β := hα.trans hαβ
  have hπ : ∀ x l, |boxP (n := n) α β x l| ≤ β := fun x l => by
    obtain ⟨h1, h2⟩ := boxP_mem hαβ x l
    rw [abs_of_nonneg (hα.trans h1)]; exact h2
  obtain ⟨L1, S1, hL1, h1⟩ := boxed_vec_lip
    (fun ij : Fin n × Fin n => fun u : SDEState n => u ij.1 * C.g ij.1 (posPart u) * C.Γ ij.2 ij.1)
    (β := β) (fun ij => prod_box_lip (hC ij.1).2 (C.Γ ij.2 ij.1) ij.1 hβ) (boxP α β) hπ
    (boxP_lip α β)
  obtain ⟨L2, S2, hL2, h2⟩ := boxed_vec_lip
    (fun i : Fin n => fun u : SDEState n => u i * C.f i (posPart u))
    (β := β) (fun i => by
      obtain ⟨L, hL, hLb⟩ := prod_box_lip (hC i).1 1 i hβ
      exact ⟨L, hL, fun u v hu hv => by simpa only [mul_one] using hLb u v hu hv⟩)
    (boxP α β) hπ (boxP_lip α β)
  have hs : ∀ x y, ‖sK C α β x - sK C α β y‖ ≤ L1 * ‖x - y‖ := fun x y => (h1 x y).1
  have hb : ∀ x y, ‖bK C α β x - bK C α β y‖ ≤ L2 * ‖x - y‖ := fun x y => (h2 x y).1
  refine ⟨LipschitzWith.continuous (K := L1.toNNReal) (LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL1]; exact hs x y),
    LipschitzWith.continuous (K := L2.toNNReal) (LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL2]; exact hb x y),
    S1 + S2, L1 + L2, by positivity, fun x => ⟨?_, ?_⟩, fun x y => ⟨?_, ?_⟩⟩
  · have := (h1 x x).2; have := (h2 x x).2
    have : ‖bK C α β x‖ ≤ S2 := (h2 x x).2
    have : 0 ≤ ‖bK C α β x‖ := norm_nonneg _
    have : ‖sK C α β x‖ ≤ S1 := (h1 x x).2
    linarith
  · have : ‖sK C α β x‖ ≤ S1 := (h1 x x).2
    have : 0 ≤ ‖sK C α β x‖ := norm_nonneg _
    have : ‖bK C α β x‖ ≤ S2 := (h2 x x).2
    linarith
  · have := hs x y; nlinarith [norm_nonneg (x - y)]
  · have := hb x y; nlinarith [norm_nonneg (x - y)]

/-- The box `[α, β]^n`. -/
def boxSet (α β : ℝ) : Set (SDEState n) := {u | ∀ l, α ≤ u l ∧ u l ≤ β}

theorem boxSet_convex (α β : ℝ) : Convex ℝ (boxSet (n := n) α β) := by
  refine fun x hx y hy a b ha hb hab => fun l => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain ⟨h1, h2⟩ := hx l
  obtain ⟨h3, h4⟩ := hy l
  have e1 : a * α + b * α = α := by rw [← add_mul, hab, one_mul]
  have e2 : a * β + b * β = β := by rw [← add_mul, hab, one_mul]
  exact ⟨by linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h3 hb],
    by linarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h4 hb]⟩

theorem boxSet_isCompact {α β : ℝ} (hα : 0 ≤ α) : IsCompact (boxSet (n := n) α β) := by
  have hc : IsClosed (boxSet (n := n) α β) := by
    have : boxSet (n := n) α β = ⋂ i, ({y : SDEState n | α ≤ y i} ∩ {y | y i ≤ β}) := by
      ext y; simp [boxSet, forall_and]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).inter
      (isClosed_le (PiLp.continuous_apply 2 _ i) continuous_const)
  refine Metric.isCompact_of_isClosed_isBounded hc ((Metric.isBounded_closedBall
    (x := (0 : SDEState n)) (r := n * β)).subset fun y hy => ?_)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_card_mul fun i => by rw [abs_of_nonneg (hα.trans (hy i).1)]; exact (hy i).2

theorem boxP_mem_boxSet {α β : ℝ} (hαβ : α ≤ β) (x : SDEState n) : boxP α β x ∈ boxSet α β :=
  fun l => boxP_mem hαβ x l

theorem posPart_of_orthant {u : SDEState n} (hu : u ∈ orthant n) : posPart u = u := by
  ext l; rw [posPart_apply']; exact max_eq_left (hu l)

/-- Assumption 1.1 part 1 makes `aK` uniformly separated from `0` with a fixed sign per
coordinate, so `|aK i x + aK i y| ≥ κ`. -/
theorem aK_sep (C : Coeffs n)
    (hpd : ∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef)
    (hgc : ∀ i, ContinuousOn (C.g i) (orthant n)) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ κ > 0, ∀ i x y, κ ≤ |aK C α β i x + aK C α β i y| := by
  set B : Set (SDEState n) := boxSet α β with hBdef
  have hBo : B ⊆ orthant n := fun u hu l => hα.le.trans (hu l).1
  have hBc : IsCompact B := boxSet_isCompact hα.le
  have hBp : IsPreconnected B := (boxSet_convex α β).isPreconnected
  have hBn : (WithLp.toLp 2 (fun _ => α) : SDEState n) ∈ B := fun l => ⟨le_rfl, hαβ⟩
  have hne : ∀ i, ∀ u ∈ orthant n, C.g i u ≠ 0 := fun i u hu e => by
    have := (hpd u hu).diag_pos (i := i)
    simp [e] at this
  have hsign : ∀ i, ∃ m > (0 : ℝ), (∀ u ∈ B, m ≤ C.g i u) ∨ (∀ u ∈ B, C.g i u ≤ -m) := by
    intro i
    have hgB : ContinuousOn (C.g i) B := (hgc i).mono hBo
    obtain ⟨u0, hu0, hmin⟩ := hBc.exists_isMinOn ⟨_, hBn⟩ (continuous_abs.comp_continuousOn hgB)
    have hm : 0 < |C.g i u0| := abs_pos.2 (hne i u0 (hBo hu0))
    have hle : ∀ u ∈ B, |C.g i u0| ≤ |C.g i u| := fun u hu => hmin hu
    refine ⟨|C.g i u0|, hm, ?_⟩
    rcases lt_or_gt_of_ne (hne i u0 (hBo hu0)) with hneg | hpos
    · right
      intro u hu
      have hu' : C.g i u < 0 := by
        by_contra hc
        push Not at hc
        obtain ⟨z, hz, hz0⟩ := hBp.intermediate_value hu0 hu hgB ⟨hneg.le, hc⟩
        exact hne i z (hBo hz) hz0
      have := hle u hu
      rw [abs_of_neg hu'] at this
      linarith
    · left
      intro u hu
      have hu' : 0 < C.g i u := by
        by_contra hc
        push Not at hc
        obtain ⟨z, hz, hz0⟩ := hBp.intermediate_value hu hu0 hgB ⟨hc, hpos.le⟩
        exact hne i z (hBo hz) hz0
      have := hle u hu
      rw [abs_of_pos hu'] at this
      linarith
  choose m hm0 hm using hsign
  have hT : 0 ≤ ∑ i, 1 / m i := Finset.sum_nonneg fun i _ => by have := hm0 i; positivity
  refine ⟨2 * α / (1 + ∑ i, 1 / m i), by positivity, fun i x y => ?_⟩
  have hκ : 2 * α / (1 + ∑ i, 1 / m i) ≤ 2 * α * m i := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 / m i ≤ ∑ j, 1 / m j :=
      Finset.single_le_sum (f := fun j => 1 / m j) (fun j _ => by have := hm0 j; positivity)
        (Finset.mem_univ i)
    have h2 : m i * (1 / m i) = 1 := by field_simp [(hm0 i).ne']
    have h3 := hm0 i
    nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]
  refine hκ.trans ?_
  have hx := boxP_mem_boxSet (n := n) hαβ x
  have hy := boxP_mem_boxSet (n := n) hαβ y
  have ex : aK C α β i x = boxP α β x i * C.g i (boxP α β x) := by
    rw [aK, posPart_of_orthant (hBo hx)]
  have ey : aK C α β i y = boxP α β y i * C.g i (boxP α β y) := by
    rw [aK, posPart_of_orthant (hBo hy)]
  rw [ex, ey]
  have hxi := (hx i).1
  have hyi := (hy i).1
  rcases hm i with hp | hn
  · have a1 := hp _ hx; have a2 := hp _ hy
    rw [abs_of_pos (by nlinarith [hm0 i])]
    nlinarith [hm0 i]
  · have a1 := hn _ hx; have a2 := hn _ hy
    rw [abs_of_neg (by nlinarith [hm0 i])]
    nlinarith [hm0 i]

theorem aK_continuous (C : Coeffs n) (hgc : ∀ i, ContinuousOn (C.g i) (orthant n)) (α β : ℝ)
    (i : Fin n) : Continuous (aK C α β i) := by
  have hpc : Continuous fun x : SDEState n => posPart (boxP α β x) :=
    continuous_posPart.comp (boxP_continuous α β)
  exact ((PiLp.continuous_apply 2 _ i).comp (boxP_continuous α β)).mul
    ((hgc i).comp_continuous hpc fun x => posPart_mem_orthant _)

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

open StochKolmogorov.Persist in
theorem gamma_isUnit {n : ℕ} (C : Coeffs n)
    (hpd : ∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef) :
    IsUnit C.Γ.det := by
  have h0 : (0 : SDEState n) ∈ orthant n := fun l => by simp
  have hP := (hpd 0 h0).det_pos
  set D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => C.g i 0) with hD
  have heq : (Matrix.of fun i j => C.g i 0 * C.g j 0 * C.sig i j) =
      D * (C.Γ.transpose * C.Γ) * D := by
    ext i j
    simp only [hD, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Coeffs.sig]
    ring
  rw [heq, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hP
  rw [isUnit_iff_ne_zero]
  intro hz
  rw [hz] at hP
  simp at hP

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

theorem box_nbhd {α β δ : ℝ} (hδ : 0 < δ) {x y : SDEState n} (hx : x ∈ boxSet α β)
    (hy : y ∈ boxSet α β) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : SDEState n)
    (hz : ‖z - (x - t • (x - y))‖ < 2 * δ) : z ∈ boxSet (α - 2 * δ) (β + 2 * δ) := by
  intro i
  have hzi : |z i - (x i - t * (x i - y i))| < 2 * δ := by
    have h := PiLp.norm_apply_le (z - (x - t • (x - y))) i
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs] at h
    exact h.trans_lt hz
  have h1 := (hx i).1
  have h2 := (hx i).2
  have h3 := (hy i).1
  have h4 := (hy i).2
  have hw1 : α ≤ x i - t * (x i - y i) := by nlinarith
  have hw2 : x i - t * (x i - y i) ≤ β := by nlinarith
  rw [abs_lt] at hzi
  constructor <;> linarith [hzi.1, hzi.2]

end C5g
end ItoLib


-- ===== R (8f909832 s7): minorization on boxes and interior reachability =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5gM
open StochKolmogorov.Persist

variable {n : ℕ}

theorem core_minor_box {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hpd : ∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ∀ T : ℝ≥0, 0 < T → T ≤ T₀ → ∃ a : ℝ, 0 < a ∧
      ∀ x ∈ boxSet α β, ∀ y ∈ boxSet α β, ∀ F : Set (SDEState n),
        Real.exp (-a) * (P.real {ω | X x T ω ∈ interior F} - 1 / 4) ≤
          P.real {ω | X y T ω ∈ F} := by
  haveI : IsProbabilityMeasure P := hX.1
  have hW := hX.2.1
  set δ : ℝ := α / 4 with hδdef
  have hδ : 0 < δ := by positivity
  set α' : ℝ := α - 2 * δ with hα'def
  set β' : ℝ := β + 2 * δ with hβ'def
  have hα' : 0 < α' := by rw [hα'def, hδdef]; linarith
  have hαβ' : α' ≤ β' := by rw [hα'def, hβ'def]; linarith
  have hgc : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hC i).2.continuousOn
  obtain ⟨hσc, hbc, s₁, b₁, S₁, L₁, hs₁, hb₁, hL₁, hSg₁, hLg₁, hag₁⟩ := kolm_trunc C hC
  obtain ⟨hs, hb, S, L, hL, hSg, hLg⟩ := kolm_box C hC hα'.le hαβ'
  obtain ⟨κ, hκ, hsep⟩ := aK_sep C hpd hgc hα' hαβ'
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hSg 0).1
  have hne : ∀ i x y, aK C α' β' i x + aK C α' β' i y ≠ 0 := fun i x y h => by
    have := hsep i x y
    rw [h, abs_zero] at this
    linarith
  set J := jInv (aK C α' β') C.Γ with hJdef
  have hJm : Measurable (Function.uncurry J) :=
    jInv_measurable C.Γ (fun i => (aK_continuous C hgc α' β' i).measurable)
  have hJ : ∀ p v, avgApply (sK C α' β') p (J p v) = v :=
    jInv_right (sK_apply C α' β') (gamma_isUnit C hpd) hne
  set Λ : ℝ := 2 * Real.sqrt (∑ j, ∑ k, (C.Γ.transpose)⁻¹ j k ^ 2) / κ with hΛdef
  have hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2 :=
    fun p v => jInv_bound C.Γ hκ hsep p v
  have hNc : IsCompact (boxSet (n := n) α' β') := boxSet_isCompact hα'.le
  obtain ⟨R₀, hR₀⟩ := hNc.isBounded.exists_norm_le
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 (boxSet_isCompact (n := n) hα.le).isBounded
  set G : ℝ := D ^ 2 with hGdef
  have hag : ∀ x ∈ boxSet α' β', (fun z : SDEState n => diffusion C (0, z)) x = sK C α' β' x ∧
      (fun z : SDEState n => drift C (0, z)) x = bK C α' β' x := by
    intro x hx
    constructor <;> simp [sK, bK, boxP_eq hx]
  set f : ℝ → ℝ := fun T => 2 * (16 * n * S ^ 2 * T / (δ / 2) ^ 2) +
      4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T)) *
        (12 * n * L ^ 2 * T + L ^ 2 * T ^ 2) / δ ^ 2 with hfdef
  have hfc : Continuous f := by rw [hfdef]; fun_prop
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hev : ∀ᶠ T in 𝓝 (0 : ℝ), f T < 1 / 8 ∧ T * S < δ / 2 := by
    refine (hfc.tendsto 0).eventually (gt_mem_nhds (by rw [hf0]; norm_num)) |>.and ?_
    have hc : Continuous fun T : ℝ => T * S := by fun_prop
    exact hc.tendsto 0 |>.eventually (gt_mem_nhds (by simpa using half_pos hδ))
  obtain ⟨ρ, hρ, hρev⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨Real.toNNReal (ρ / 2), Real.toNNReal_pos.2 (by positivity), ?_⟩
  intro T hT hTT
  have hT0 : 0 < (T : ℝ) := NNReal.coe_pos.2 hT
  have hTT' : (T : ℝ) ≤ ρ / 2 := by
    have := NNReal.coe_le_coe.2 hTT
    rwa [Real.coe_toNNReal _ (by positivity)] at this
  have hdist : dist (T : ℝ) 0 < ρ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hT0]; linarith
  obtain ⟨hfT, hTS⟩ := hρev hdist
  set X3 : ℝ := Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T) / (2 * T)
    with hX3
  have hX30 : 0 ≤ X3 := by rw [hX3]; positivity
  set a : ℝ := 8 * (X3 + 1) with hadef
  have ha : 0 < a := by rw [hadef]; positivity
  have hE3 : (X3 + 1) / a = 1 / 8 := by
    rw [hadef]; field_simp
  refine ⟨a, ha, ?_⟩
  intro x hx y hy F
  have hxo : x ∈ orthant n := fun i => hα.le.trans (hx i).1
  have hyo : y ∈ orthant n := fun i => hα.le.trans (hy i).1
  have hG : ‖x - y‖ ^ 2 ≤ G := by
    rw [hGdef, ← dist_eq_norm]
    exact pow_le_pow_left₀ dist_nonneg (hD hx hy) 2
  have hsmall : 2 * (16 * n * S ^ 2 * T / (δ / 2) ^ 2) +
      4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T)) *
        (12 * n * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 +
      (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T) / (2 * T) + 1) / a ≤
        1 / 4 := by
    have h1 : f T < 1 / 8 := hfT
    rw [hfdef] at h1
    rw [← hX3, hE3]
    linarith
  have hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ →
      z ∈ boxSet α' β' := fun t ht0 ht1 z hz => box_nbhd hδ hx hy ht0 ht1 z hz
  exact EthierKurtz.brownian_sde_local_minorization hW hσc hbc x y (hX.2.2 x hxo) (hX.2.2 y hyo)
    hs₁ hb₁ hL₁ hSg₁ hLg₁ hag₁ hs hb hJm hJ hL hSg hLg hΛ hag (fun z hz => hR₀ z hz) subset_rfl
    hNc.isClosed.measurableSet hG hT0 hδ ha hTS.le hBx hsmall F

end C5gM
end ItoLib

namespace StochKolmogorov.Classify.Reach
open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ}

/-- a positive lower corner for two points of the open orthant -/
theorem exists_box (x u : SDEState n) (hx : x ∈ openOrthant n) (hu : u ∈ openOrthant n) :
    ∃ α β : ℝ, 0 < α ∧ α ≤ β ∧ x ∈ ItoLib.boxSet α β ∧ u ∈ ItoLib.boxSet α β := by
  classical
  set A : Finset ℝ := insert 1 (Finset.univ.image fun i => min (x i) (u i)) with hA
  set Bs : Finset ℝ := insert 1 (Finset.univ.image fun i => max (x i) (u i)) with hB
  have hAne : A.Nonempty := Finset.insert_nonempty _ _
  have hBne : Bs.Nonempty := Finset.insert_nonempty _ _
  refine ⟨A.min' hAne, Bs.max' hBne, ?_, ?_, ?_, ?_⟩
  · have hm := A.min'_mem hAne
    rcases Finset.mem_insert.1 hm with h | hm'
    · rw [h]; norm_num
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hm'
      rw [← hi]; exact lt_min (hx i) (hu i)
  · exact (A.min'_le 1 (Finset.mem_insert_self _ _)).trans (Bs.le_max' 1 (Finset.mem_insert_self _ _))
  · intro i
    have h1 : min (x i) (u i) ∈ A := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have h2 : max (x i) (u i) ∈ Bs := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    exact ⟨(A.min'_le _ h1).trans (min_le_left _ _), (le_max_left _ _).trans (Bs.le_max' _ h2)⟩
  · intro i
    have h1 : min (x i) (u i) ∈ A := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have h2 : max (x i) (u i) ∈ Bs := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    exact ⟨(A.min'_le _ h1).trans (min_le_right _ _), (le_max_right _ _).trans (Bs.le_max' _ h2)⟩

/-- small times: the solution from `u` is in the open set `U ∋ u` with probability `> 1/4` -/
theorem exists_small_time {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ≥0 → Ω → SDEState n) (u : SDEState n) (hc : ∀ ω, Continuous fun t => Y t ω)
    (h0 : Y 0 =ᵐ[P] fun _ => u) (U : Set (SDEState n)) (hUo : IsOpen U) (hu : u ∈ U)
    (T₀ : ℝ≥0) (hT₀ : 0 < T₀) :
    ∃ T : ℝ≥0, 0 < T ∧ T ≤ T₀ ∧ (1 / 4 : ℝ) < P.real {ω | Y T ω ∈ U} := by
  set Tk : ℕ → ℝ≥0 := fun k => T₀ / ((k + 1 : ℕ) : ℝ≥0) with hTk
  have hTlim : Tendsto Tk atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (T₀ : ℝ)).comp (tendsto_add_atTop_nat 1)
    have h' : Tendsto (fun k => ((Tk k : ℝ≥0) : ℝ)) atTop (𝓝 ((0 : ℝ≥0) : ℝ)) := by
      rw [NNReal.coe_zero]
      refine h.congr (fun k => ?_)
      simp only [hTk, Function.comp_apply, NNReal.coe_div, NNReal.coe_natCast]
    exact NNReal.tendsto_coe.1 h'
  set A : ℕ → Set Ω := fun k => {ω | ∀ j, k ≤ j → Y (Tk j) ω ∈ U} with hAdef
  have hAm : Monotone A := fun k l hkl ω hω j hj => hω j (hkl.trans hj)
  have hcov : ∀ᵐ ω ∂P, ω ∈ ⋃ k, A k := by
    filter_upwards [h0] with ω hω
    have ht : Tendsto (fun j => Y (Tk j) ω) atTop (𝓝 u) := by
      have := ((hc ω).tendsto 0).comp hTlim
      rw [hω] at this
      exact this
    obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 (ht (hUo.mem_nhds hu))
    exact Set.mem_iUnion.2 ⟨k, fun j hj => hk j hj⟩
  have h1 : P (⋃ k, A k) = 1 := by
    rw [← measure_univ (μ := P)]
    exact measure_congr (Filter.eventuallyEq_univ.2 hcov)
  rw [hAm.measure_iUnion] at h1
  have hlt : (1 / 4 : ℝ≥0∞) < ⨆ k, P (A k) := by
    rw [h1]; norm_num
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hlt
  have hk1 : (1 : ℝ≥0) ≤ ((k + 1 : ℕ) : ℝ≥0) := by exact_mod_cast Nat.succ_pos k
  refine ⟨Tk k, div_pos hT₀ (by positivity), div_le_self (zero_le (a := T₀)) hk1, ?_⟩
  have hsub : A k ⊆ {ω | Y (Tk k) ω ∈ U} := fun ω hω => hω k le_rfl
  have h2 : (1 / 4 : ℝ≥0∞) < P {ω | Y (Tk k) ω ∈ U} := hk.trans_le (measure_mono hsub)
  have h3 : ((1 / 4 : ℝ≥0∞)).toReal < (P {ω | Y (Tk k) ω ∈ U}).toReal :=
    (ENNReal.toReal_lt_toReal (by norm_num) (measure_ne_top _ _)).2 h2
  have h4 : ((1 / 4 : ℝ≥0∞)).toReal = 1 / 4 := by norm_num
  rw [h4] at h3
  exact h3

end StochKolmogorov.Classify.Reach

open StochKolmogorov.Classify EthierKurtz in
theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : StochKolmogorov.Classify.Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hpd : ∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef) :
    ∀ x ∈ openOrthant n, ∀ U : Set (SDEState n), IsOpen U → U.Nonempty →
      U ⊆ openOrthant n → ∃ t : ℝ≥0, 0 < P {ω | X x t ω ∈ U} := by
  intro x hx U hUo hUne hUsub
  haveI : IsProbabilityMeasure P := hX.1
  obtain ⟨u, hu⟩ := hUne
  have huo : u ∈ openOrthant n := hUsub hu
  obtain ⟨α, β, hα, hαβ, hxb, hub⟩ := Reach.exists_box x u hx huo
  let C' : StochKolmogorov.Persist.Coeffs n := ⟨C.f, C.g, C.Γ⟩
  have hX' : StochKolmogorov.Persist.IsSolutionFamily P C' B X := hX
  obtain ⟨T₀, hT₀, hT⟩ := ItoLib.core_minor_box P C' B X hX' hC hpd hα hαβ
  have huo' : u ∈ orthant n := fun i => (huo i).le
  have hsol := hX.2.2 u huo'
  obtain ⟨T, hT0, hTT, hTp⟩ := Reach.exists_small_time P (X u) u hsol.2.1 hsol.2.2.2.1 U hUo hu T₀ hT₀
  obtain ⟨a, ha, hmin⟩ := hT T hT0 hTT
  have h := hmin u hub x hxb U
  rw [hUo.interior_eq] at h
  have hpos : 0 < Real.exp (-a) * (P.real {ω | X u T ω ∈ U} - 1 / 4) :=
    mul_pos (Real.exp_pos _) (by linarith)
  have hr : 0 < P.real {ω | X x T ω ∈ U} := hpos.trans_le h
  refine ⟨T, ?_⟩
  exact pos_iff_ne_zero.2 (fun h0 => by simp [Measure.real, h0] at hr)
