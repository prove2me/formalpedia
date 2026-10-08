-- Prove2me | solution 1 for PiIrrationality.zeilberger_zudilin_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T06:48:21.683336+00:00
-- url     : https://prove2.me/submissions/305cefef-3076-46a6-b623-505daa15bd63

import Definitions.Def_PiIrrationality_UpperBound
import Definitions.Def_PiIrrationality_ZZEvenForms
import Theorems.Thm_PiIrrationality_ZZEven_linearForm
import Theorems.Thm_PiIrrationality_ZZEven_phi_lower
import Theorems.Thm_PiIrrationality_lcmUpto_le_exp
import Theorems.Thm_PiIrrationality_ratio_linearForm_upperBound
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The Zeilberger–Zudilin bound `μ(π) ≤ 7.103205334138`

The even Zeilberger–Zudilin linear forms `M_n J_n = U_n + V_n π`
(`PiIrrationality.ZZEven.linearForm`) feed Hata's ratio lemma
(`PiIrrationality.ratio_linearForm_upperBound`). Each exponential rate is used at its
certified sharp value: the integral decays at the saddle-point rate `τ = 7.0495458479305`
(two exact Bernstein certificates on a polygon through a lattice point next to the saddle),
the coefficient grows at `17.2114784916918` from above and `17.2114784916916` from below
(the saddle-point bound and a single multinomial term at scale `10⁷`), and the deleted
primes save `1.29055122046966` per `n` (`phi_lower` with `K = 10²⁰`, tail bounded by a
telescoping rational function). Logarithms are certified by the `artanh` series.
-/

/-! ## Part `LogBounds` -/

section
/-!
# Certified bounds for logarithms of rationals

`log ((1+y)/(1-y)) = Σ 2 y^{2k+1}/(2k+1)`, with an explicit geometric tail.
-/

namespace ZZRec

open Real

/-- The partial sum of the `artanh` series. -/
noncomputable def lsum (y : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, 2 * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1)

lemma log_ratio_hasSum {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * y ^ (2 * k + 1))
      (log ((1 + y) / (1 - y))) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := y) (by rw [abs_of_nonneg hy0]; exact hy1)
  rw [Real.log_div (by linarith) (by linarith)]
  exact h

lemma lsum_le_log {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (N : ℕ) :
    lsum y N ≤ log ((1 + y) / (1 - y)) := by
  apply sum_le_hasSum (Finset.range N) _ (log_ratio_hasSum hy0 hy1)
  intro k _
  positivity

lemma log_le_lsum {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (N : ℕ) :
    log ((1 + y) / (1 - y)) ≤ lsum y N + 2 * y ^ (2 * N + 1) / ((2 * N + 1) * (1 - y ^ 2)) := by
  have hs := log_ratio_hasSum hy0 hy1
  have hy2 : y ^ 2 < 1 := by nlinarith
  rw [← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add N]
  unfold lsum
  gcongr
  -- the tail
  have hg : HasSum (fun k : ℕ => 2 / (2 * (N : ℝ) + 1) * y ^ (2 * N + 1) * (y ^ 2) ^ k)
      (2 / (2 * (N : ℝ) + 1) * y ^ (2 * N + 1) * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left _
  calc ∑' k, (2 : ℝ) * (1 / (2 * ((k + N : ℕ) : ℝ) + 1)) * y ^ (2 * (k + N) + 1)
      ≤ ∑' k : ℕ, 2 / (2 * (N : ℝ) + 1) * y ^ (2 * N + 1) * (y ^ 2) ^ k := by
        refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff N).mpr hs.summable)
          hg.summable
        have hk : (2 : ℝ) * (1 / (2 * ((k + N : ℕ) : ℝ) + 1)) ≤ 2 / (2 * (N : ℝ) + 1) := by
          rw [mul_one_div]
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        have hp : y ^ (2 * (k + N) + 1) = y ^ (2 * N + 1) * (y ^ 2) ^ k := by
          rw [← pow_mul, ← pow_add]; congr 1; ring
        rw [hp, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (by positivity))
          (by positivity)
    _ = 2 * y ^ (2 * N + 1) / ((2 * N + 1) * (1 - y ^ 2)) := by
        rw [hg.tsum_eq]; field_simp

/-- Two-sided bounds for `log r`, `r > 0`, through `y = (r-1)/(r+1)` when `r ≥ 1`. -/
lemma log_bounds_of_ge_one {r : ℝ} (hr : 1 ≤ r) (N : ℕ) :
    lsum ((r - 1) / (r + 1)) N ≤ log r ∧
      log r ≤ lsum ((r - 1) / (r + 1)) N +
        2 * ((r - 1) / (r + 1)) ^ (2 * N + 1) / ((2 * N + 1) * (1 - ((r - 1) / (r + 1)) ^ 2)) := by
  have hy0 : 0 ≤ (r - 1) / (r + 1) := div_nonneg (by linarith) (by linarith)
  have hy1 : (r - 1) / (r + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have he : (1 + (r - 1) / (r + 1)) / (1 - (r - 1) / (r + 1)) = r := by
    field_simp; ring
  have h1 := lsum_le_log hy0 hy1 N
  have h2 := log_le_lsum hy0 hy1 N
  rw [he] at h1 h2
  exact ⟨h1, h2⟩

end ZZRec

end

/-! ## Part `IntegralSharp` -/

section
/-!
# The integral `J_n` decays at the exact saddle-point rate

The contour is moved to the polygon `-1-2i → p̄ → 0 → p → -1+2i`, where `p` is a rational
point within `10⁻⁷` (on the grid `2⁻²⁴ ℤ[i]`) of the saddle point `s ≈ -0.354 + 1.430 i` of
`f(t) = t⁴ (t⁴+6t²+25)⁴ / (25-t²)⁶`. On every edge `|f| ≤ ρ`, certified by exact Bernstein
expansions, with `ρ = 17356059646937919 / 2·10¹⁹`, which exceeds `|f(s)|` by a relative `2·10⁻¹⁴`.
-/

open Complex Metric

namespace PiIrrationality.ZZEven.SharpIntegral

/-- `ρ·|25-t²|⁶ - |t|⁴ |t⁴+6t²+25|⁴` in real coordinates. -/
noncomputable def Pxy (x y : ℝ) : ℝ :=
  (17356059646937919 / 20000000000000000000 : ℝ) * ((25 - x ^ 2 + y ^ 2) ^ 2 + (2 * x * y) ^ 2) ^ 3 -
    (x ^ 2 + y ^ 2) ^ 2 *
      (((x ^ 2 - y ^ 2) ^ 2 - 4 * x ^ 2 * y ^ 2 + 6 * (x ^ 2 - y ^ 2) + 25) ^ 2 +
        (4 * x * y * (x ^ 2 - y ^ 2) + 12 * x * y) ^ 2) ^ 2

/-- The bound `ρ`. -/
noncomputable def ρ : ℝ := 17356059646937919 / 20000000000000000000

lemma Pxy_neg (x y : ℝ) : Pxy x (-y) = Pxy x y := by unfold Pxy; ring

lemma cert_pv4_0 (u : ℝ) (h0 : (0 : ℝ) ≤ u) (h1 : u ≤ (1 : ℝ)) :
    0 ≤ Pxy ((-5939287 / 16777216 : ℝ) + u * (-10837929 / 16777216 : ℝ)) ((23992435 / 16777216 : ℝ) + u * (9561997 / 16777216 : ℝ)) := by
  have h : Pxy ((-5939287 / 16777216 : ℝ) + u * (-10837929 / 16777216 : ℝ)) ((23992435 / 16777216 : ℝ) + u * (9561997 / 16777216 : ℝ)) =
      (383257295862537660006599362717013426606746852159154477610376471271500133824435378942439037323324475195333242793317555390605139902764283797052996731 / 58147097943648551243945904631040362748291308854985444822519215934451143049071833866095284057101085244861001728501294234682768130289172480000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 0 * ((1 : ℝ) - u) ^ 20 +
      (6756788718586785313171473117554443826670796411373343054652392670723334442199584544101307810690667475974915688347317502539715005860580234845016647 / 1732918558825509287236508865089427314647773172109885359481549737884138317378516014399984003815087236310869506850877232393108848640000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 1 * ((1 : ℝ) - u) ^ 19 +
      (62284363414176747955575774648452651480092415406941985851532721264090879251608292163640335655455625856229781598561895888566021422013310462640837223 / 103289995123476343586236766880120474973188231713168940513226374261625904880673647785185814131205513257436126878909899735040000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 2 * ((1 : ℝ) - u) ^ 18 +
      (142627431327772900331789799058287259791810702807260771780784275011341991982723254032977412636353313377877466805541075535830967159146319610499 / 12313126936373274753837200031294879314087418522020452083733841688826788053592878316066958204651536137752071246970880000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 3 * ((1 : ℝ) - u) ^ 17 +
      (307020103572699077638774460965188104264862211415255022490531408333514114312916227418274578462468599277824803960817234608324786993988779 / 2935678228467291534861850745986671284219603186135399838384113714415261281393260554329623747980960878789918720000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 4 * ((1 : ℝ) - u) ^ 16 +
      (12888186791445537384153337412057520583459071605494966921870615431977774710232978800894027314514595396587673318495856612632649291 / 21872507247830119243725022271176213653531694308932124364257706064099529991993759232235131770230538240000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 5 * ((1 : ℝ) - u) ^ 15 +
      (1512016570403550969806228762954094473100162426964534901235454668271571632801231525639495434355255766104441491518695467197 / 651851512427035547605902620291001011536469885973099600203564943793402015924267745978687160320000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 6 * ((1 : ℝ) - u) ^ 14 +
      (32869420554868273709017039629830941891678302827659736240428228116125328405244589755244718691421979172760890385781 / 4856672230564322677298654767058797266606017097630348803129531024347260713013021245440000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 7 * ((1 : ℝ) - u) ^ 13 +
      (2354597473139695444786126675884401346705434755088330603712074371837534477536265828168092455091853302122893683640743 / 155413511378058325673556952545881512531392547124171161700144992779112342816416679854080000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 8 * ((1 : ℝ) - u) ^ 12 +
      (123068747261944882656399707270723480304185466902592388306494699625517809929545647434586371344776918096494741 / 4631683569492647816942839400347516314130799386625622561578303360316525185597440000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 9 * ((1 : ℝ) - u) ^ 11 +
      (10202122522109971324681903055199067646795527769845638316083395973627364176990799575177510675969622193 / 276069853871622551497390234491081018098044358886815462206500968951971840000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 10 * ((1 : ℝ) - u) ^ 10 +
      (168643836182684178165510048809374440346937075526551739067335507438653167392434942582727946863 / 4113761393303015105387422956393376262456839664083949658371522560000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 11 * ((1 : ℝ) - u) ^ 9 +
      (17799410429704772763048005725062889655711218643852098971784836532373630137114166144109 / 490398573077084434674671048688098938757996519098752696320000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 12 * ((1 : ℝ) - u) ^ 8 +
      (373311174879651045602773246809818953558214123033602486757333927783078723441073 / 14615016373309029182036848327162830196559325429760000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 13 * ((1 : ℝ) - u) ^ 7 +
      (12337316599421871538477546939764997914472239965131941172482177379994677 / 871122859317602466466238995025326621327360000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 14 * ((1 : ℝ) - u) ^ 6 +
      (15836315757062239265395577757243237935418724956669328220839827 / 2596148429267413814265248164610048000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 15 * ((1 : ℝ) - u) ^ 5 +
      (61858780046345091203555712227534387869614936982725059 / 30948500982134506872478105600000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 16 * ((1 : ℝ) - u) ^ 4 +
      (44548352491891419437659682952677437037611971 / 92233720368547758080000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 17 * ((1 : ℝ) - u) ^ 3 +
      (89903362295127502803387055816168587 / 1099511627776000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 18 * ((1 : ℝ) - u) ^ 2 +
      (28653978117574751432655933 / 3276800000000000000 : ℝ) * (u - (0 : ℝ)) ^ 19 * ((1 : ℝ) - u) ^ 1 +
      (17356059646937919 / 39062500000 : ℝ) * (u - (0 : ℝ)) ^ 20 * ((1 : ℝ) - u) ^ 0 := by
    unfold Pxy; ring
  rw [h]
  have a : 0 ≤ u - (0 : ℝ) := by linarith
  have b : 0 ≤ (1 : ℝ) - u := by linarith
  positivity

lemma cert_pv4 (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 ≤ Pxy ((-5939287 / 16777216 : ℝ) + u * (-10837929 / 16777216 : ℝ)) ((23992435 / 16777216 : ℝ) + u * (9561997 / 16777216 : ℝ)) := by
  exact cert_pv4_0 u (by linarith) (by linarith)

lemma cert_p0_0 (u : ℝ) (h0 : (0 : ℝ) ≤ u) (h1 : u ≤ (1 : ℝ)) :
    0 ≤ Pxy ((-5939287 / 16777216 : ℝ) + u * (5939287 / 16777216 : ℝ)) ((23992435 / 16777216 : ℝ) + u * (-23992435 / 16777216 : ℝ)) := by
  have h : Pxy ((-5939287 / 16777216 : ℝ) + u * (5939287 / 16777216 : ℝ)) ((23992435 / 16777216 : ℝ) + u * (-23992435 / 16777216 : ℝ)) =
      (383257295862537660006599362717013426606746852159154477610376471271500133824435378942439037323324475195333242793317555390605139902764283797052996731 / 58147097943648551243945904631040362748291308854985444822519215934451143049071833866095284057101085244861001728501294234682768130289172480000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 0 * ((1 : ℝ) - u) ^ 20 +
      (30783731066340103172413608080907234548138209968419259672598292157180770539141530416899782647450477204820817656631372908365139084643041669 / 6455624695217271474139797930007529685824264482073058782076648391351619055042102986574113383200344578589757929931868733440000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 1 * ((1 : ℝ) - u) ^ 19 +
      (13172955330255604542891257435113104101398892302114644420071701158233156340519553171828178703079152653239328288217165443871643434013960002893676933 / 12911249390434542948279595860015059371648528964146117564153296782703238110084205973148226766400689157179515859863737466880000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 2 * ((1 : ℝ) - u) ^ 18 +
      (3432094547995720015505366924482445427344005990422572621014055841172194507682321028199744170526911753630550552483025132475069774831019 / 183479889279205720928865671624166955263725199133462489899007107150953830087078784645601484248810054924369920000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 3 * ((1 : ℝ) - u) ^ 17 +
      (23266757165823996914867165459658097697324868814931509961382384848836356359362057210477589188126056112242131722278488796294747131086319 / 146783911423364576743092537299333564210980159306769991919205685720763064069663027716481187399048043939495936000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 4 * ((1 : ℝ) - u) ^ 16 +
      (269907360259359451936912762707580692454662126327513637239965007384326502099959564600465501627495414971583237467296373437 / 325925756213517773802951310145500505768234942986549800101782471896701007962133872989343580160000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 5 * ((1 : ℝ) - u) ^ 15 +
      (1952187872274455162966978155417778521771351098458166228050551883057007837677460542475864857109623859473432499265879105087 / 651851512427035547605902620291001011536469885973099600203564943793402015924267745978687160320000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 6 * ((1 : ℝ) - u) ^ 14 +
      (154799110213675687432231581094216836774984581742502867235383528926423103909877711499762507729437056118665399421351 / 19426688922257290709194619068235189066424068390521395212518124097389042852052084981760000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 7 * ((1 : ℝ) - u) ^ 13 +
      (2512971532124118466255767092680116200429738993103692263644624308976608293602588583931985999815658860810493119613351 / 155413511378058325673556952545881512531392547124171161700144992779112342816416679854080000000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 8 * ((1 : ℝ) - u) ^ 12 +
      (14127917845903719827953421120144516449220803272807035668963284717431847670776826780700656439825319 / 552139707743245102994780468982162036196088717773630924413001937903943680000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 9 * ((1 : ℝ) - u) ^ 11 +
      (176775128174430561247756211485533043990091541226937787366481472523608425498838464159938429489681319 / 5521397077432451029947804689821620361960887177736309244130019379039436800000000000000000 : ℝ) * (u - (0 : ℝ)) ^ 10 * ((1 : ℝ) - u) ^ 10 +
      (20046247274818492450475335168147112665211513734614291460323778413619040210554717371 / 627710173538668076383578942320766641610235544446403451289600000000000000 : ℝ) * (u - (0 : ℝ)) ^ 11 * ((1 : ℝ) - u) ^ 9 +
      (64009845084915652549666210632051391001552067963816880255911019599856897587311630057 / 2510840694154672305534315769283066566440942177785613805158400000000000000 : ℝ) * (u - (0 : ℝ)) ^ 12 * ((1 : ℝ) - u) ^ 8 +
      (363242451247807321732264729700337418732112498579597537992791317269 / 22300745198530623141535718272648361505980416000000000000 : ℝ) * (u - (0 : ℝ)) ^ 13 * ((1 : ℝ) - u) ^ 7 +
      (369995420418581547669907064077216845052519680741092891229911518467 / 44601490397061246283071436545296723011960832000000000000 : ℝ) * (u - (0 : ℝ)) ^ 14 * ((1 : ℝ) - u) ^ 6 +
      (42279937961779786869756262671983259608744728027553 / 12676506002282294014967032053760000000000 : ℝ) * (u - (0 : ℝ)) ^ 15 * ((1 : ℝ) - u) ^ 5 +
      (210857026625551237618923233213853968092024028881313 / 202824096036516704239472512860160000000000 : ℝ) * (u - (0 : ℝ)) ^ 16 * ((1 : ℝ) - u) ^ 4 +
      (4382619794050046556726950438114991 / 18014398509481984000000000 : ℝ) * (u - (0 : ℝ)) ^ 17 * ((1 : ℝ) - u) ^ 3 +
      (1453839350866340615548646203530999 / 36028797018963968000000000 : ℝ) * (u - (0 : ℝ)) ^ 18 * ((1 : ℝ) - u) ^ 2 +
      (17356059646937919 / 4096000000 : ℝ) * (u - (0 : ℝ)) ^ 19 * ((1 : ℝ) - u) ^ 1 +
      (17356059646937919 / 81920000000 : ℝ) * (u - (0 : ℝ)) ^ 20 * ((1 : ℝ) - u) ^ 0 := by
    unfold Pxy; ring
  rw [h]
  have a : 0 ≤ u - (0 : ℝ) := by linarith
  have b : 0 ≤ (1 : ℝ) - u := by linarith
  positivity

lemma cert_p0 (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 ≤ Pxy ((-5939287 / 16777216 : ℝ) + u * (5939287 / 16777216 : ℝ)) ((23992435 / 16777216 : ℝ) + u * (-23992435 / 16777216 : ℝ)) := by
  exact cert_p0_0 u (by linarith) (by linarith)

/-- The pointwise saddle estimate from a nonnegative certificate. -/
lemma G_le (t : ℂ) (h : 0 ≤ Pxy t.re t.im) :
    ‖t‖ ^ 4 * ‖t ^ 4 + 6 * t ^ 2 + 25‖ ^ 4 ≤ ρ * ‖25 - t ^ 2‖ ^ 6 := by
  have h1 : ‖t‖ ^ 2 = t.re ^ 2 + t.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h2 : ‖t ^ 4 + 6 * t ^ 2 + 25‖ ^ 2 =
      ((t.re ^ 2 - t.im ^ 2) ^ 2 - 4 * t.re ^ 2 * t.im ^ 2 + 6 * (t.re ^ 2 - t.im ^ 2) + 25) ^ 2 +
        (4 * t.re * t.im * (t.re ^ 2 - t.im ^ 2) + 12 * t.re * t.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [add_re, add_im, mul_re, mul_im, pow_succ, pow_zero, one_mul, re_ofNat, im_ofNat]
    ring
  have h3 : ‖25 - t ^ 2‖ ^ 2 = (25 - t.re ^ 2 + t.im ^ 2) ^ 2 + (2 * t.re * t.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, mul_re, mul_im, pow_succ, pow_zero, one_mul, re_ofNat, im_ofNat]
    ring
  unfold Pxy at h
  unfold ρ
  have e1 : ‖t‖ ^ 4 = (‖t‖ ^ 2) ^ 2 := by ring
  have e2 : ‖t ^ 4 + 6 * t ^ 2 + 25‖ ^ 4 = (‖t ^ 4 + 6 * t ^ 2 + 25‖ ^ 2) ^ 2 := by ring
  have e3 : ‖25 - t ^ 2‖ ^ 6 = (‖25 - t ^ 2‖ ^ 2) ^ 3 := by ring
  rw [e1, e2, e3, h1, h2, h3]
  linarith

/-- `R n` is holomorphic on the open disc of radius 5. -/
lemma R_differentiableOn (n : ℕ) : DifferentiableOn ℂ (R n) (ball 0 5) := by
  intro z hz
  have hz' : ‖z‖ < 5 := by simpa using hz
  have hne : (25 - z ^ 2 : ℂ) ≠ 0 := by
    intro h0
    have : ‖z ^ 2‖ = 25 := by
      rw [show z ^ 2 = 25 by linear_combination -h0]; norm_num
    rw [norm_pow] at this
    nlinarith [norm_nonneg z]
  apply DifferentiableAt.differentiableWithinAt
  have hd : DifferentiableAt ℂ (fun t : ℂ => 5 * t ^ (4 * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (4 * n) /
      (25 - t ^ 2) ^ (6 * n + 1)) z :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero _ hne)
  exact hd

lemma ρ_pos : 0 < ρ := by unfold ρ; norm_num

/-- Pointwise bound for `R n` at a certified point of norm at most `√5`. -/
lemma norm_R_le (n : ℕ) (t : ℂ) (hP : 0 ≤ Pxy t.re t.im) (ht : ‖t‖ ^ 2 ≤ 5) :
    ‖R n t‖ ≤ 5 / 20 * ρ ^ n := by
  have hD : 20 ≤ ‖25 - t ^ 2‖ := by
    have h1 : ‖(25 : ℂ)‖ ≤ ‖25 - t ^ 2‖ + ‖t ^ 2‖ := by
      calc ‖(25 : ℂ)‖ = ‖(25 - t ^ 2) + t ^ 2‖ := by ring_nf
        _ ≤ ‖25 - t ^ 2‖ + ‖t ^ 2‖ := norm_add_le _ _
    rw [norm_pow] at h1
    norm_num at h1
    linarith
  have hDpos : 0 < ‖25 - t ^ 2‖ := by linarith
  have hG := G_le t hP
  have hρ := ρ_pos
  unfold R
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
  have h5 : ‖(5 : ℂ)‖ = 5 := by norm_num
  rw [h5, pow_mul ‖t‖ 4 n, pow_mul ‖t ^ 4 + 6 * t ^ 2 + 25‖ 4 n, pow_succ ‖25 - t ^ 2‖ (6 * n),
    pow_mul ‖25 - t ^ 2‖ 6 n]
  have hA : (‖t‖ ^ 4) ^ n * (‖t ^ 4 + 6 * t ^ 2 + 25‖ ^ 4) ^ n ≤
      ρ ^ n * (‖25 - t ^ 2‖ ^ 6) ^ n := by
    rw [← mul_pow (‖t‖ ^ 4), ← mul_pow ρ]
    exact pow_le_pow_left₀ (by positivity) hG n
  have hB : 0 < (‖25 - t ^ 2‖ ^ 6) ^ n := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc 5 * (‖t‖ ^ 4) ^ n * (‖t ^ 4 + 6 * t ^ 2 + 25‖ ^ 4) ^ n
      = 5 * ((‖t‖ ^ 4) ^ n * (‖t ^ 4 + 6 * t ^ 2 + 25‖ ^ 4) ^ n) := by ring
    _ ≤ 5 * (ρ ^ n * (‖25 - t ^ 2‖ ^ 6) ^ n) := by gcongr
    _ ≤ 5 / 20 * ρ ^ n * ((‖25 - t ^ 2‖ ^ 6) ^ n * ‖25 - t ^ 2‖) := by
      have : (0 : ℝ) ≤ ρ ^ n * (‖25 - t ^ 2‖ ^ 6) ^ n := by positivity
      nlinarith

/-- Fundamental theorem of calculus along an affine path inside the disc. -/
lemma path_ftc (n : ℕ) {F : ℂ → ℂ} (hF : ∀ z ∈ ball (0 : ℂ) 5, HasDerivAt F (R n z) z)
    (p v : ℂ) (α β : ℝ) (hαβ : α ≤ β)
    (hmem : ∀ s ∈ Set.Icc α β, p + (s : ℂ) * v ∈ ball (0 : ℂ) 5) :
    ∫ s in α..β, R n (p + (s : ℂ) * v) * v = F (p + (β : ℂ) * v) - F (p + (α : ℂ) * v) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    rw [Set.uIcc_of_le hαβ] at hs
    have h1 : HasDerivAt (fun w : ℂ => p + w * v) v (s : ℂ) := by
      simpa using ((hasDerivAt_id (s : ℂ)).mul_const v).const_add p
    have h2 := (hF _ (hmem s hs)).comp (s : ℂ) h1
    exact h2.comp_ofReal
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hαβ]
    apply ContinuousOn.mul _ continuousOn_const
    exact ((R_differentiableOn n).continuousOn).comp (by fun_prop) (fun s hs => hmem s hs)

/-- Convexity of `‖·‖²` along a segment. -/
lemma normSq_seg_le (a b : ℂ) (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) (ha : ‖a‖ ^ 2 ≤ 5)
    (hb : ‖b‖ ^ 2 ≤ 5) : ‖a + (u : ℂ) * (b - a)‖ ^ 2 ≤ 5 := by
  rw [Complex.sq_norm, Complex.normSq_apply] at *
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, zero_mul,
    sub_zero, add_zero] at *
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1), sq_nonneg (b.re - a.re), sq_nonneg (b.im - a.im)]

lemma mem_ball_of_normSq {t : ℂ} (h : ‖t‖ ^ 2 ≤ 5) : t ∈ ball (0 : ℂ) 5 := by
  rw [mem_ball, dist_zero_right]
  nlinarith [norm_nonneg t]

/-- The vertices of the polygon. -/
noncomputable def v0 : ℂ := ⟨-1, -2⟩
noncomputable def w1 : ℂ := ⟨-5939287 / 16777216, -23992435 / 16777216⟩
noncomputable def w2 : ℂ := ⟨0, 0⟩
noncomputable def w3 : ℂ := ⟨-5939287 / 16777216, 23992435 / 16777216⟩
noncomputable def v4 : ℂ := ⟨-1, 2⟩

lemma seg_re_im (a b : ℂ) (u : ℝ) :
    (a + (u : ℂ) * (b - a)).re = a.re + u * (b.re - a.re) ∧
      (a + (u : ℂ) * (b - a)).im = a.im + u * (b.im - a.im) := by
  constructor <;> simp

lemma cert_edge3 (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 ≤ Pxy (w3 + (u : ℂ) * (v4 - w3)).re (w3 + (u : ℂ) * (v4 - w3)).im := by
  obtain ⟨hr, hi⟩ := seg_re_im w3 v4 u
  rw [hr, hi]; simp only [w3, v4]
  have := cert_pv4 u h0 h1
  convert this using 2 <;> ring

lemma cert_edge2 (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 ≤ Pxy (w2 + (u : ℂ) * (w3 - w2)).re (w2 + (u : ℂ) * (w3 - w2)).im := by
  obtain ⟨hr, hi⟩ := seg_re_im w2 w3 u
  rw [hr, hi]; simp only [w2, w3]
  have := cert_p0 (1 - u) (by linarith) (by linarith)
  convert this using 2 <;> ring

lemma cert_edge1 (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 ≤ Pxy (w1 + (u : ℂ) * (w2 - w1)).re (w1 + (u : ℂ) * (w2 - w1)).im := by
  obtain ⟨hr, hi⟩ := seg_re_im w1 w2 u
  rw [hr, hi, ← Pxy_neg]; simp only [w1, w2]
  have := cert_p0 u h0 h1
  convert this using 2 <;> ring

lemma cert_edge0 (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 ≤ Pxy (v0 + (u : ℂ) * (w1 - v0)).re (v0 + (u : ℂ) * (w1 - v0)).im := by
  obtain ⟨hr, hi⟩ := seg_re_im v0 w1 u
  rw [hr, hi, ← Pxy_neg]; simp only [v0, w1]
  have := cert_pv4 (1 - u) (by linarith) (by linarith)
  convert this using 2 <;> ring

lemma normSq_v (z : ℂ) (x y : ℝ) (hz : z = ⟨x, y⟩) : ‖z‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [hz, Complex.sq_norm, Complex.normSq_apply]; ring

lemma norm_le_of_sq {z : ℂ} {L : ℝ} (hL : 0 ≤ L) (h : ‖z‖ ^ 2 ≤ L ^ 2) : ‖z‖ ≤ L :=
  abs_le_of_sq_le_sq' h hL |>.2 |> fun h' => by
    have := norm_nonneg z; nlinarith [sq_nonneg (‖z‖ - L), sq_nonneg (‖z‖ + L)]

/-- One edge contributes at most `(5/20) ρ^n ‖b - a‖`. -/
lemma edge_bound (n : ℕ) {F : ℂ → ℂ} (hF : ∀ z ∈ ball (0 : ℂ) 5, HasDerivAt F (R n z) z)
    (a b : ℂ) (ha : ‖a‖ ^ 2 ≤ 5) (hb : ‖b‖ ^ 2 ≤ 5)
    (hcert : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ Pxy (a + (u : ℂ) * (b - a)).re (a + (u : ℂ) * (b - a)).im) :
    ‖F b - F a‖ ≤ 5 / 20 * ρ ^ n * ‖b - a‖ := by
  have hftc := path_ftc n hF a (b - a) 0 1 zero_le_one (fun s hs =>
    mem_ball_of_normSq (normSq_seg_le a b s hs.1 hs.2 ha hb))
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero,
    add_sub_cancel] at hftc
  rw [← hftc]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := 5 / 20 * ρ ^ n * ‖b - a‖)
    (f := fun s : ℝ => R n (a + (s : ℂ) * (b - a)) * (b - a)) (by
      intro u hu
      rw [Set.uIoc_of_le zero_le_one] at hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_R_le n _ (hcert u hu.1.le hu.2)
        (normSq_seg_le a b u hu.1.le hu.2 ha hb)) (norm_nonneg _))
  simpa using this

/-- **`‖J_n‖ ≤ 2 ρ^n`.** -/
theorem norm_J_le (n : ℕ) : ‖J n‖ ≤ 2 * ρ ^ n := by
  obtain ⟨F, hF⟩ := (R_differentiableOn n).isExactOn_ball
  have hvert := path_ftc n hF (-1) Complex.I (-2) 2 (by norm_num) (fun s hs => by
    apply mem_ball_of_normSq
    rw [normSq_v _ (-1) s (by apply Complex.ext <;> simp)]
    nlinarith [hs.1, hs.2])
  rw [intervalIntegral.integral_mul_const] at hvert
  have e4 : (-1 : ℂ) + ((2 : ℝ) : ℂ) * Complex.I = v4 := by apply Complex.ext <;> simp [v4]
  have e0 : (-1 : ℂ) + ((-2 : ℝ) : ℂ) * Complex.I = v0 := by apply Complex.ext <;> simp [v0]
  rw [e4, e0] at hvert
  have hJ : ‖J n‖ = ‖F v4 - F v0‖ := by
    unfold J
    rw [norm_neg, ← hvert, norm_mul, Complex.norm_I, mul_one]
  have n0 : ‖v0‖ ^ 2 ≤ 5 := by rw [normSq_v v0 (-1) (-2) rfl]; norm_num
  have n1 : ‖w1‖ ^ 2 ≤ 5 := by rw [normSq_v w1 _ _ rfl]; norm_num
  have n2 : ‖w2‖ ^ 2 ≤ 5 := by rw [normSq_v w2 _ _ rfl]; norm_num
  have n3 : ‖w3‖ ^ 2 ≤ 5 := by rw [normSq_v w3 _ _ rfl]; norm_num
  have n4 : ‖v4‖ ^ 2 ≤ 5 := by rw [normSq_v v4 (-1) 2 rfl]; norm_num
  have b0 := edge_bound n hF v0 w1 n0 n1 cert_edge0
  have b1 := edge_bound n hF w1 w2 n1 n2 cert_edge1
  have b2 := edge_bound n hF w2 w3 n2 n3 cert_edge2
  have b3 := edge_bound n hF w3 v4 n3 n4 cert_edge3
  have l0 : ‖w1 - v0‖ ≤ 1 := norm_le_of_sq (by norm_num) (by
    rw [normSq_v (w1 - v0) (1 - 5939287 / 16777216) (2 - 23992435 / 16777216)
      (by apply Complex.ext <;> simp [v0, w1] <;> norm_num)]
    norm_num)
  have l1 : ‖w2 - w1‖ ≤ 3 / 2 := norm_le_of_sq (by norm_num) (by
    rw [normSq_v (w2 - w1) (5939287 / 16777216) (23992435 / 16777216)
      (by apply Complex.ext <;> simp [w1, w2] <;> norm_num)]
    norm_num)
  have l2 : ‖w3 - w2‖ ≤ 3 / 2 := norm_le_of_sq (by norm_num) (by
    rw [normSq_v (w3 - w2) (-5939287 / 16777216) (23992435 / 16777216)
      (by apply Complex.ext <;> simp [w2, w3] <;> norm_num)]
    norm_num)
  have l3 : ‖v4 - w3‖ ≤ 1 := norm_le_of_sq (by norm_num) (by
    rw [normSq_v (v4 - w3) (-1 + 5939287 / 16777216) (2 - 23992435 / 16777216)
      (by apply Complex.ext <;> simp [w3, v4] <;> norm_num)]
    norm_num)
  have hsplit : F v4 - F v0 = (F w1 - F v0) + (F w2 - F w1) + (F w3 - F w2) + (F v4 - F w3) := by ring
  have hg : (0 : ℝ) ≤ 5 / 20 * ρ ^ n := by have := ρ_pos; positivity
  have htot : ‖F v4 - F v0‖ ≤ 5 / 20 * ρ ^ n * 5 := by
    rw [hsplit]
    calc ‖(F w1 - F v0) + (F w2 - F w1) + (F w3 - F w2) + (F v4 - F w3)‖
        ≤ ‖F w1 - F v0‖ + ‖F w2 - F w1‖ + ‖F w3 - F w2‖ + ‖F v4 - F w3‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ 5 / 20 * ρ ^ n * ‖w1 - v0‖ + 5 / 20 * ρ ^ n * ‖w2 - w1‖ +
          5 / 20 * ρ ^ n * ‖w3 - w2‖ + 5 / 20 * ρ ^ n * ‖v4 - w3‖ := by
          gcongr
      _ ≤ 5 / 20 * ρ ^ n * 5 := by
          nlinarith [mul_le_mul_of_nonneg_left l0 hg, mul_le_mul_of_nonneg_left l1 hg,
            mul_le_mul_of_nonneg_left l2 hg, mul_le_mul_of_nonneg_left l3 hg]
  rw [hJ]
  have := ρ_pos
  calc ‖F v4 - F v0‖ ≤ 5 / 20 * ρ ^ n * 5 := htot
    _ ≤ 2 * ρ ^ n := by nlinarith [pow_nonneg this.le n]

end PiIrrationality.ZZEven.SharpIntegral

end

/-! ## Part `CoefLeSharp` -/

section
/-!
# Sharp upper rate for `coef n`

`coef n ≤ σ(x₀)ⁿ` with `σ(x) = A(x) / (x⁶ (1-x)⁸)` at `x₀ = 256891719/2³⁰`, within `10⁻⁹` of the
saddle point; `log σ(x₀) ≤ 17.2114784916918`.
-/

open Polynomial

namespace PiIrrationality.ZZEven.CoefLe

/-- A single term of the negative binomial series is at most its sum. -/
lemma choose_mul_pow_le (d j : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (Nat.choose (j + d) d : ℝ) * x ^ j ≤ ((1 - x)⁻¹) ^ (d + 1) := by
  have hnorm : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  have h := hasSum_choose_mul_geometric_of_norm_lt_one' (R := ℝ) d hnorm
  have hinv : Ring.inverse (1 - x) = (1 - x)⁻¹ := Ring.inverse_eq_inv _
  rw [hinv] at h
  exact le_hasSum h j fun i _ => by positivity

/-- The real evaluation of `A`. -/
noncomputable def Aval (x : ℝ) : ℝ :=
  (1 + x) ^ 4 * (2 + 6 * x + 9 * x ^ 2 + 6 * x ^ 3 + 2 * x ^ 4) ^ 4

lemma eval₂_A (x : ℝ) : (A.eval₂ (Nat.castRingHom ℝ) x) = Aval x := by
  simp [A, Aval, eval₂_mul, eval₂_pow, eval₂_add, eval₂_X, eval₂_one]

/-- Partial sums of a polynomial with natural coefficients are below its value. -/
lemma partial_le_eval (p : ℕ[X]) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∑ k ∈ Finset.range m, (p.coeff k : ℝ) * x ^ k ≤ p.eval₂ (Nat.castRingHom ℝ) x := by
  rw [eval₂_eq_sum_range' (Nat.castRingHom ℝ) (n := p.natDegree + m + 1) (by omega)]
  simp only [Nat.coe_castRingHom]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
  · intro k _ _; positivity

theorem coef_le_pow (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (coef n : ℝ) ≤ (Aval x / (x ^ 6 * (1 - x) ^ 8)) ^ n := by
  have h1x : 0 < 1 - x := by linarith
  have h1x' : 1 - x ≠ 0 := h1x.ne'
  have hx' : x ≠ 0 := hx0.ne'
  unfold coef
  push_cast
  have hterm : ∀ k ∈ Finset.range (6 * n + 1),
      ((A ^ n).coeff k : ℝ) * (Nat.choose (8 * n - 1 + (6 * n - k)) (6 * n - k) : ℝ) ≤
        ((A ^ n).coeff k : ℝ) * x ^ k * (x ^ (6 * n))⁻¹ * ((1 - x)⁻¹) ^ (8 * n) := by
    intro k hk
    have hk' : k ≤ 6 * n := by simpa [Nat.lt_succ_iff] using hk
    have hc := choose_mul_pow_le (8 * n - 1) (6 * n - k) hx0.le hx1
    rw [show 8 * n - 1 + 1 = 8 * n by omega] at hc
    rw [show 8 * n - 1 + (6 * n - k) = (6 * n - k) + (8 * n - 1) by ring,
      Nat.choose_symm_add]
    have hxk : x ^ k * (x ^ (6 * n))⁻¹ = (x ^ (6 * n - k))⁻¹ := by
      rw [show 6 * n = (6 * n - k) + k by omega, pow_add]
      field_simp
      rw [show 6 * n - k + k - k = 6 * n - k by omega]
    have hcoef : (0 : ℝ) ≤ ((A ^ n).coeff k : ℝ) := Nat.cast_nonneg _
    rw [mul_assoc ((A ^ n).coeff k : ℝ), mul_assoc ((A ^ n).coeff k : ℝ)]
    apply mul_le_mul_of_nonneg_left _ hcoef
    rw [hxk]
    have hpos : 0 < x ^ (6 * n - k) := pow_pos hx0 _
    rw [le_inv_mul_iff₀ hpos, mul_comm]
    exact hc
  calc ∑ k ∈ Finset.range (6 * n + 1),
        ((A ^ n).coeff k : ℝ) * (Nat.choose (8 * n - 1 + (6 * n - k)) (6 * n - k) : ℝ)
      ≤ ∑ k ∈ Finset.range (6 * n + 1),
          ((A ^ n).coeff k : ℝ) * x ^ k * (x ^ (6 * n))⁻¹ * ((1 - x)⁻¹) ^ (8 * n) :=
        Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range (6 * n + 1), ((A ^ n).coeff k : ℝ) * x ^ k) *
          ((x ^ (6 * n))⁻¹ * ((1 - x)⁻¹) ^ (8 * n)) := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ (A ^ n).eval₂ (Nat.castRingHom ℝ) x * ((x ^ (6 * n))⁻¹ * ((1 - x)⁻¹) ^ (8 * n)) := by
        apply mul_le_mul_of_nonneg_right (partial_le_eval _ _ hx0.le); positivity
    _ = (Aval x / (x ^ 6 * (1 - x) ^ 8)) ^ n := by
        rw [eval₂_pow, eval₂_A, div_pow, mul_pow, ← pow_mul, ← pow_mul]
        field_simp
        rw [one_div_pow, mul_assoc, one_div_mul_cancel (pow_ne_zero _ h1x'), mul_one]

end PiIrrationality.ZZEven.CoefLe

namespace PiIrrationality.ZZEven.CoefLe

lemma log_two_le : Real.log 2 ≤ 0.69314718055994531 := by
  have h := (ZZRec.log_bounds_of_ge_one (r := 2) (by norm_num) 18).2
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

lemma log_r_le : Real.log (88940638466852907017 / 50000000000000000000) ≤ 0.57594615825302432 := by
  have h := (ZZRec.log_bounds_of_ge_one (r := 88940638466852907017 / 50000000000000000000)
    (by norm_num) 18).2
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

lemma sigma_le : Aval (256891719 / 1073741824) /
    ((256891719 / 1073741824) ^ 6 * (1 - 256891719 / 1073741824) ^ 8) ≤
      2 ^ 24 * (88940638466852907017 / 50000000000000000000 : ℝ) := by
  unfold Aval; norm_num

lemma log_sigma_le : Real.log (2 ^ 24 * (88940638466852907017 / 50000000000000000000 : ℝ)) ≤
    17.2114784916918 := by
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have := log_two_le
  have := log_r_le
  push_cast
  linarith

end PiIrrationality.ZZEven.CoefLe

open PiIrrationality.ZZEven PiIrrationality.ZZEven.CoefLe in
/-- **Sharp upper rate**: `coef n ≤ exp(17.2114784916918 n)`. -/
theorem PiIrrationality.ZZEven.coef_le_sharp (n : ℕ) :
    (coef n : ℝ) ≤ Real.exp (17.2114784916918 * (n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coef, A]
  have h := coef_le_pow n hn (x := 256891719 / 1073741824) (by norm_num) (by norm_num)
  refine h.trans ?_
  have hσ0 : (0 : ℝ) ≤ Aval (256891719 / 1073741824) /
      ((256891719 / 1073741824) ^ 6 * (1 - 256891719 / 1073741824) ^ 8) := by
    unfold Aval; positivity
  have hσ : Aval (256891719 / 1073741824) /
      ((256891719 / 1073741824) ^ 6 * (1 - 256891719 / 1073741824) ^ 8) ≤
        Real.exp 17.2114784916918 := by
    refine sigma_le.trans ?_
    rw [← Real.exp_log (show (0 : ℝ) < 2 ^ 24 * (88940638466852907017 / 50000000000000000000) by
      norm_num)]
    exact Real.exp_le_exp.mpr log_sigma_le
  calc _ ≤ (Real.exp 17.2114784916918) ^ n := pow_le_pow_left₀ hσ0 hσ n
    _ = Real.exp (17.2114784916918 * (n : ℝ)) := by
        rw [← Real.exp_nat_mul]; ring_nf

end

/-! ## Part `CoefGeSharp` -/

section
open Polynomial Filter

namespace PiIrrationality.ZZEven.CoefGeSharp


/-- The binomial term `T(i) = C(N,i) M^i (N-M)^(N-i)`. -/
def T (N M i : ℕ) : ℕ := N.choose i * M ^ i * (N - M) ^ (N - i)

lemma T_step (N M i : ℕ) (hi : i < N) :
    T N M (i + 1) * ((i + 1) * (N - M)) = T N M i * ((N - i) * M) := by
  unfold T
  have h1 := Nat.choose_succ_right_eq N i
  obtain ⟨k, hk⟩ : ∃ k, N - i = k + 1 := ⟨N - i - 1, by omega⟩
  have hk' : N - (i + 1) = k := by omega
  rw [hk] at h1
  rw [hk, hk']
  calc N.choose (i + 1) * M ^ (i + 1) * (N - M) ^ k * ((i + 1) * (N - M))
      = (N.choose (i + 1) * (i + 1)) * M ^ i * M * (N - M) ^ k * (N - M) := by ring
    _ = (N.choose i * (k + 1)) * M ^ i * M * (N - M) ^ k * (N - M) := by rw [h1]
    _ = N.choose i * M ^ i * (N - M) ^ (k + 1) * ((k + 1) * M) := by ring

lemma T_mono_up (N M : ℕ) (hMN : M ≤ N) : ∀ i, i < M → T N M i ≤ T N M (i + 1) := by
  intro i hi
  rcases Nat.eq_or_lt_of_le hMN with h | h
  · -- N = M: T i = 0 for i < N
    unfold T
    have h0 : N - M = 0 := by omega
    rw [h0, zero_pow (show N - i ≠ 0 by omega)]
    simp
  · have hpos : 0 < (i + 1) * (N - M) := Nat.mul_pos (by omega) (by omega)
    have hstep := T_step N M i (by omega)
    have hineq : (i + 1) * (N - M) ≤ (N - i) * M := by
      have e : (N - i) * M = (i + 1) * (N - M) + (N * (M - (i + 1)) + M) := by
        zify [show i ≤ N by omega, hMN, show i + 1 ≤ M by omega]
        ring
      omega
    by_contra hcon
    push Not at hcon
    have : T N M (i + 1) * ((i + 1) * (N - M)) < T N M i * ((i + 1) * (N - M)) :=
      Nat.mul_lt_mul_of_pos_right hcon hpos
    have : T N M i * ((i + 1) * (N - M)) ≤ T N M i * ((N - i) * M) :=
      Nat.mul_le_mul_left _ hineq
    omega

lemma T_mono_down (N M : ℕ) (hMN : M ≤ N) :
    ∀ i, M ≤ i → i < N → T N M (i + 1) ≤ T N M i := by
  intro i hi hiN
  have hpos : 0 < (i + 1) * (N - M) := Nat.mul_pos (by omega) (by omega)
  have hstep := T_step N M i hiN
  have hineq : (N - i) * M ≤ (i + 1) * (N - M) := by
    have e : (i + 1) * (N - M) = (N - i) * M + (N * (i + 1 - M) - M) := by
      have h3 : M ≤ N * (i + 1 - M) := by
        calc M ≤ N := hMN
          _ = N * 1 := (mul_one N).symm
          _ ≤ N * (i + 1 - M) := Nat.mul_le_mul_left _ (by omega)
      zify [show i ≤ N by omega, hMN, show M ≤ i + 1 by omega, h3]
      ring
    omega
  by_contra hcon
  push Not at hcon
  have : T N M i * ((i + 1) * (N - M)) < T N M (i + 1) * ((i + 1) * (N - M)) :=
    Nat.mul_lt_mul_of_pos_right hcon hpos
  have : T N M i * ((N - i) * M) ≤ T N M i * ((i + 1) * (N - M)) := Nat.mul_le_mul_left _ hineq
  omega

lemma T_up (N M : ℕ) (hMN : M ≤ N) (i : ℕ) :
    ∀ d, i + d ≤ M → T N M i ≤ T N M (i + d) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h
    calc T N M i ≤ T N M (i + d) := ih (by omega)
      _ ≤ T N M (i + d + 1) := T_mono_up N M hMN (i + d) (by omega)
      _ = T N M (i + (d + 1)) := by ring_nf

lemma T_down (N M : ℕ) (hMN : M ≤ N) :
    ∀ d, M + d ≤ N → T N M (M + d) ≤ T N M M := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h
    calc T N M (M + (d + 1)) = T N M (M + d + 1) := by ring_nf
      _ ≤ T N M (M + d) := T_mono_down N M hMN (M + d) (by omega) (by omega)
      _ ≤ T N M M := ih (by omega)

lemma T_le_mode (N M : ℕ) (hMN : M ≤ N) : ∀ i, i ≤ N → T N M i ≤ T N M M := by
  intro i hiN
  rcases le_or_gt i M with h | h
  · have := T_up N M hMN i (M - i) (by omega)
    rwa [Nat.add_sub_cancel' h] at this
  · have := T_down N M hMN (i - M) (by omega)
    rwa [Nat.add_sub_cancel' h.le] at this

/-- The entropy lower bound for binomial coefficients, in `ℕ`. -/
theorem pow_le_choose_mul (N M : ℕ) (hMN : M ≤ N) :
    N ^ N ≤ (N + 1) * (N.choose M * M ^ M * (N - M) ^ (N - M)) := by
  have hsum : N ^ N = ∑ i ∈ Finset.range (N + 1), T N M i := by
    have := add_pow (M : ℕ) (N - M) N
    rw [Nat.add_sub_cancel' hMN] at this
    rw [this]
    apply Finset.sum_congr rfl
    intro i _
    simp only [T, Nat.cast_id]; ring
  rw [hsum]
  calc ∑ i ∈ Finset.range (N + 1), T N M i ≤ ∑ _i ∈ Finset.range (N + 1), T N M M :=
        Finset.sum_le_sum fun i hi => T_le_mode N M hMN i (by simpa [Nat.lt_succ_iff] using hi)
    _ = (N + 1) * T N M M := by simp
    _ = (N + 1) * (N.choose M * M ^ M * (N - M) ^ (N - M)) := rfl


/-! ### Coefficient lower bounds in `ℕ[X]` -/

/-- A coefficient of a product is at least the product of two coefficients. -/
lemma coeff_mul_ge (f g : ℕ[X]) (a b : ℕ) : f.coeff a * g.coeff b ≤ (f * g).coeff (a + b) := by
  rw [coeff_mul]
  exact Finset.single_le_sum (f := fun x : ℕ × ℕ => f.coeff x.1 * g.coeff x.2)
    (fun _ _ => Nat.zero_le _)
    (show (a, b) ∈ Finset.antidiagonal (a + b) from Finset.mem_antidiagonal.mpr rfl)

/-- One term of the binomial expansion bounds the coefficient of a power of a sum. -/
lemma coeff_add_pow_ge (p r : ℕ[X]) (m j k : ℕ) :
    (p ^ j * r ^ (m - j)).coeff k * m.choose j ≤ ((p + r) ^ m).coeff k := by
  rcases le_or_gt j m with hj | hj
  · rw [add_pow, finsetSum_coeff]
    have := Finset.single_le_sum (f := fun i => (p ^ i * r ^ (m - i) * (m.choose i : ℕ[X])).coeff k)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    simpa [coeff_mul_natCast] using this
  · simp [Nat.choose_eq_zero_of_lt hj]

lemma two_eq : (C 2 : ℕ[X]) = 2 := by simp [map_ofNat]

lemma A_eq : A =
    (1 + X) ^ 4 * ((X * (X + C 2) + C 2) ^ 4 * ((C 2 * X) * (X + 1) + 1) ^ 4) := by
  unfold A
  simp only [map_ofNat]
  ring

lemma A_pow (n : ℕ) : A ^ n =
    (1 + X) ^ (4 * n) * ((X * (X + C 2) + C 2) ^ (4 * n) * ((C 2 * X) * (X + 1) + 1) ^ (4 * n)) := by
  rw [A_eq, mul_pow, mul_pow, pow_mul, pow_mul, pow_mul]

/-- The `(X^2+2X+2)^m` coefficient at `j + l`. -/
lemma coeff_P1 (m j l : ℕ) :
    m.choose j * 2 ^ (m - j) * (2 ^ (j - l) * j.choose l) ≤
      ((X * (X + C 2) + C 2 : ℕ[X]) ^ m).coeff (j + l) := by
  refine le_trans ?_ (coeff_add_pow_ge _ _ m j (j + l))
  rw [mul_pow, ← C_pow, mul_assoc, coeff_mul_C, add_comm j l, coeff_X_pow_mul,
    coeff_X_add_C_pow]
  apply le_of_eq; simp only [Nat.cast_id]; ring

/-- The `(2X^2+2X+1)^m` coefficient at `j + l`. -/
lemma coeff_P2 (m j l : ℕ) :
    m.choose j * (2 ^ j * j.choose l) ≤ (((C 2 * X) * (X + 1) + 1 : ℕ[X]) ^ m).coeff (j + l) := by
  refine le_trans ?_ (coeff_add_pow_ge _ _ m j (j + l))
  rw [one_pow, mul_one, mul_pow, mul_pow, ← C_pow, mul_assoc, coeff_C_mul, add_comm j l,
    coeff_X_pow_mul, coeff_X_add_one_pow]
  apply le_of_eq; simp only [Nat.cast_id]; ring

/-- `C(N+a, M+b) ≥ C(N, M)` whenever `b ≤ a`. -/
lemma choose_le_choose_add (N M a b : ℕ) (hab : b ≤ a) :
    N.choose M ≤ (N + a).choose (M + b) := by
  have h1 : ∀ b, N.choose M ≤ (N + b).choose (M + b) := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      calc N.choose M ≤ (N + b).choose (M + b) := ih
        _ ≤ (N + b).choose (M + b) + (N + b).choose (M + b + 1) := Nat.le_add_right _ _
        _ = (N + (b + 1)).choose (M + (b + 1)) := by
          rw [show N + (b + 1) = (N + b) + 1 by ring, show M + (b + 1) = (M + b) + 1 by ring,
            Nat.choose_succ_succ]
  calc N.choose M ≤ (N + b).choose (M + b) := h1 b
    _ ≤ (N + a).choose (M + b) := Nat.choose_le_choose _ (by omega)

/-- The single-term lower bound for `coef n` with `q = n / 10000000`. -/
theorem coef_ge_term (n : ℕ) (hq1 : 1 ≤ n / 10000000) :
    let q := n / 10000000
    (40000000 * q).choose (7722388 * q) *
      (((40000000 * q).choose (8451002 * q) * 2 ^ (31548998 * q) * (2 ^ (7548068 * q) * (8451002 * q).choose (902934 * q))) *
        ((40000000 * q).choose (14889803 * q) * (2 ^ (14889803 * q) * (14889803 * q).choose (2874621 * q)))) *
      (105159252 * q - 1).choose (25159252 * q) ≤ coef n := by
  intro q
  have hq : 1 ≤ q := hq1
  have hn : n = 10000000 * q + n % 10000000 := (Nat.div_add_mod n 10000000).symm
  set r := n % 10000000
  have hr : r < 10000000 := Nat.mod_lt _ (by norm_num)
  have hk : 34840748 * q ∈ Finset.range (6 * n + 1) := by
    rw [Finset.mem_range]; omega
  have hterm := Finset.single_le_sum (f := fun k =>
      (A ^ n).coeff k * Nat.choose (8 * n - 1 + (6 * n - k)) (6 * n - k))
      (fun _ _ => Nat.zero_le _) hk
  refine le_trans ?_ hterm
  apply Nat.mul_le_mul
  · have hsplit : A ^ n = A ^ (10000000 * q) * A ^ r := by rw [← pow_add, ← hn]
    have hA0 : 1 ≤ (A ^ r).coeff 0 := by
      rw [coeff_zero_eq_eval_zero, eval_pow]
      apply Nat.one_le_pow
      unfold A; simp [map_ofNat]
    calc _ ≤ (A ^ (10000000 * q)).coeff (34840748 * q) := ?_
      _ ≤ (A ^ (10000000 * q)).coeff (34840748 * q) * (A ^ r).coeff 0 := Nat.le_mul_of_pos_right _ hA0
      _ ≤ (A ^ n).coeff (34840748 * q) := by rw [hsplit]; exact coeff_mul_ge _ _ _ 0
    rw [A_pow, show 4 * (10000000 * q) = 40000000 * q by ring]
    have e : 34840748 * q = 7722388 * q + ((8451002 * q + 902934 * q) + (14889803 * q + 2874621 * q)) := by ring
    rw [e]
    refine le_trans ?_ (coeff_mul_ge _ _ _ _)
    apply Nat.mul_le_mul (by rw [coeff_one_add_X_pow, Nat.cast_id])
    refine le_trans ?_ (coeff_mul_ge _ _ _ _)
    apply Nat.mul_le_mul
    · have := coeff_P1 (40000000 * q) (8451002 * q) (902934 * q)
      rw [show 40000000 * q - 8451002 * q = 31548998 * q by omega, show 8451002 * q - 902934 * q = 7548068 * q by omega] at this
      exact this
    · exact coeff_P2 (40000000 * q) (14889803 * q) (2874621 * q)
  · have e1 : 8 * n - 1 + (6 * n - 34840748 * q) = (105159252 * q - 1) + 14 * r := by omega
    have e2 : 6 * n - 34840748 * q = 25159252 * q + 6 * r := by omega
    rw [e1, e2]
    exact choose_le_choose_add _ _ _ _ (by omega)

noncomputable def E (α β : ℕ) : ℝ := (α : ℝ) ^ α / ((β : ℝ) ^ β * ((α - β : ℕ) : ℝ) ^ (α - β))

lemma E_pos (α β : ℕ) (h : β < α) (hβ : 0 < β) : 0 < E α β := by
  unfold E
  have : (0 : ℝ) < ((α - β : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt h
  have : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have : (0 : ℝ) < (α : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le β) h)
  positivity

/-- Scaled entropy bound: `E(α,β)^q ≤ (αq+1) C(αq, βq)`. -/
lemma choose_ge_real (α β q : ℕ) (h : β < α) (hβ : 0 < β) (hq : 0 < q) :
    E α β ^ q ≤ ((α * q + 1 : ℕ) : ℝ) * ((α * q).choose (β * q) : ℝ) := by
  have hnat := pow_le_choose_mul (α * q) (β * q) (Nat.mul_le_mul_right q h.le)
  have hsub : α * q - β * q = (α - β) * q := (Nat.sub_mul α β q).symm
  rw [hsub] at hnat
  have hR : ((α * q : ℕ) : ℝ) ^ (α * q) ≤ ((α * q + 1 : ℕ) : ℝ) *
      (((α * q).choose (β * q) : ℝ) * ((β * q : ℕ) : ℝ) ^ (β * q) *
        (((α - β) * q : ℕ) : ℝ) ^ ((α - β) * q)) := by exact_mod_cast hnat
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast hβ
  have hαβ : (0 : ℝ) < ((α - β : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt h
  have hqpow : (0 : ℝ) < (q : ℝ) ^ (α * q) := pow_pos hq0 _
  -- rewrite both sides with q^(αq) factored out
  have hl : ((α * q : ℕ) : ℝ) ^ (α * q) = ((α : ℝ) ^ α) ^ q * (q : ℝ) ^ (α * q) := by
    push_cast; rw [mul_pow, ← pow_mul]
  have hαeq : α * q = β * q + (α - β) * q := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' h.le]
  have hr : ((β * q : ℕ) : ℝ) ^ (β * q) * (((α - β) * q : ℕ) : ℝ) ^ ((α - β) * q) =
      ((β : ℝ) ^ β * ((α - β : ℕ) : ℝ) ^ (α - β)) ^ q * (q : ℝ) ^ (α * q) := by
    rw [hαeq, pow_add]
    push_cast
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    ring
  rw [hl, mul_assoc ((α * q).choose (β * q) : ℝ), hr] at hR
  have hden : 0 < (β : ℝ) ^ β * ((α - β : ℕ) : ℝ) ^ (α - β) := by positivity
  unfold E
  rw [div_pow, div_le_iff₀ (pow_pos hden q)]
  have := le_of_mul_le_mul_right (a := (q : ℝ) ^ (α * q))
    (by calc ((α : ℝ) ^ α) ^ q * (q : ℝ) ^ (α * q) ≤ _ := hR
      _ = ((α * q + 1 : ℕ) : ℝ) * ((α * q).choose (β * q) : ℝ) *
          ((β : ℝ) ^ β * ((α - β : ℕ) : ℝ) ^ (α - β)) ^ q * (q : ℝ) ^ (α * q) := by ring) hqpow
  linarith

/-- The constant `R` of the single-term bound. -/
noncomputable def Rc : ℝ := E 40000000 7722388 * E 40000000 8451002 * E 8451002 902934 * E 40000000 14889803 * E 14889803 2874621 * E 105159252 25159252 * 2 ^ 53986869

/-- The single term, in real form: `Rc^q ≤ D(q) · coef n`. -/
lemma Rc_pow_le (n : ℕ) (hq1 : 1 ≤ n / 10000000) :
    Rc ^ (n / 10000000) ≤ ((40000000 * (n / 10000000) + 1 : ℕ) : ℝ) ^ 3 * ((8451002 * (n / 10000000) + 1 : ℕ) : ℝ) *
      ((14889803 * (n / 10000000) + 1 : ℕ) : ℝ) * ((105159252 * (n / 10000000) + 1 : ℕ) : ℝ) * (105159252 / 80000000) *
      (coef n : ℝ) := by
  set q := n / 10000000 with hqdef
  have hq : 0 < q := hq1
  have hterm := coef_ge_term n hq1
  simp only at hterm
  rw [← hqdef] at hterm
  have hterm' : ((40000000 * q).choose (7722388 * q) : ℝ) * ((40000000 * q).choose (8451002 * q) : ℝ) *
      ((8451002 * q).choose (902934 * q) : ℝ) * ((40000000 * q).choose (14889803 * q) : ℝ) * ((14889803 * q).choose (2874621 * q) : ℝ) *
      ((105159252 * q - 1).choose (25159252 * q) : ℝ) * (2 : ℝ) ^ (53986869 * q) ≤ (coef n : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hterm
    push_cast at this
    calc _ = ((40000000 * q).choose (7722388 * q) : ℝ) *
          (((40000000 * q).choose (8451002 * q) : ℝ) * 2 ^ (31548998 * q) * (2 ^ (7548068 * q) * ((8451002 * q).choose (902934 * q) : ℝ)) *
            (((40000000 * q).choose (14889803 * q) : ℝ) * (2 ^ (14889803 * q) * ((14889803 * q).choose (2874621 * q) : ℝ)))) *
          ((105159252 * q - 1).choose (25159252 * q) : ℝ) := by
            rw [show 53986869 * q = 31548998 * q + 7548068 * q + 14889803 * q by ring, pow_add, pow_add]; ring
      _ ≤ (coef n : ℝ) := this
  have hNB : ((105159252 * q).choose (25159252 * q) : ℝ) * 80000000 ≤ ((105159252 * q - 1).choose (25159252 * q) : ℝ) * 105159252 := by
    have hc := Nat.choose_mul_succ_eq (105159252 * q - 1) (25159252 * q)
    rw [show 105159252 * q - 1 + 1 = 105159252 * q by omega, show 105159252 * q - 25159252 * q = 80000000 * q by omega] at hc
    have hc' : ((105159252 * q - 1).choose (25159252 * q) : ℝ) * (105159252 * q) = ((105159252 * q).choose (25159252 * q) : ℝ) * (80000000 * q) := by
      exact_mod_cast hc
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    nlinarith
  have e0 := choose_ge_real 40000000 7722388 q (by norm_num) (by norm_num) hq
  have e1 := choose_ge_real 40000000 8451002 q (by norm_num) (by norm_num) hq
  have e2 := choose_ge_real 8451002 902934 q (by norm_num) (by norm_num) hq
  have e3 := choose_ge_real 40000000 14889803 q (by norm_num) (by norm_num) hq
  have e4 := choose_ge_real 14889803 2874621 q (by norm_num) (by norm_num) hq
  have e5 := choose_ge_real 105159252 25159252 q (by norm_num) (by norm_num) hq
  have p0 := E_pos 40000000 7722388 (by norm_num) (by norm_num)
  have p1 := E_pos 40000000 8451002 (by norm_num) (by norm_num)
  have p2 := E_pos 8451002 902934 (by norm_num) (by norm_num)
  have p3 := E_pos 40000000 14889803 (by norm_num) (by norm_num)
  have p4 := E_pos 14889803 2874621 (by norm_num) (by norm_num)
  have p5 := E_pos 105159252 25159252 (by norm_num) (by norm_num)
  have hRc : Rc ^ q = E 40000000 7722388 ^ q * E 40000000 8451002 ^ q * E 8451002 902934 ^ q * E 40000000 14889803 ^ q * E 14889803 2874621 ^ q * E 105159252 25159252 ^ q * (2 : ℝ) ^ (53986869 * q) := by
    unfold Rc; rw [pow_mul]; simp only [mul_pow]
  rw [hRc]
  have hprod := mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul e0 e1 (pow_pos p1 q).le
    (by positivity)) e2 (pow_pos p2 q).le (by positivity)) e3 (pow_pos p3 q).le (by positivity)) e4
    (pow_pos p4 q).le (by positivity)) e5 (pow_pos p5 q).le (by positivity)
  have h2 : (0 : ℝ) < 2 ^ (53986869 * q) := by positivity
  have hfinal := mul_le_mul_of_nonneg_right hprod h2.le
  refine le_trans hfinal ?_
  calc _ = ((40000000 * q + 1 : ℕ) : ℝ) ^ 3 * ((8451002 * q + 1 : ℕ) : ℝ) * ((14889803 * q + 1 : ℕ) : ℝ) *
        ((105159252 * q + 1 : ℕ) : ℝ) *
        (((40000000 * q).choose (7722388 * q) : ℝ) * ((40000000 * q).choose (8451002 * q) : ℝ) * ((8451002 * q).choose (902934 * q) : ℝ) * ((40000000 * q).choose (14889803 * q) : ℝ) * ((14889803 * q).choose (2874621 * q) : ℝ) * ((105159252 * q).choose (25159252 * q) : ℝ) * (2 : ℝ) ^ (53986869 * q)) := by ring
    _ ≤ ((40000000 * q + 1 : ℕ) : ℝ) ^ 3 * ((8451002 * q + 1 : ℕ) : ℝ) * ((14889803 * q + 1 : ℕ) : ℝ) *
        ((105159252 * q + 1 : ℕ) : ℝ) * (105159252 / 80000000) *
        (((40000000 * q).choose (7722388 * q) : ℝ) * ((40000000 * q).choose (8451002 * q) : ℝ) * ((8451002 * q).choose (902934 * q) : ℝ) * ((40000000 * q).choose (14889803 * q) : ℝ) * ((14889803 * q).choose (2874621 * q) : ℝ) * ((105159252 * q - 1).choose (25159252 * q) : ℝ) * (2 : ℝ) ^ (53986869 * q)) := by
        have hX : (0 : ℝ) ≤ ((40000000 * q + 1 : ℕ) : ℝ) ^ 3 * ((8451002 * q + 1 : ℕ) : ℝ) *
            ((14889803 * q + 1 : ℕ) : ℝ) * ((105159252 * q + 1 : ℕ) : ℝ) := by positivity
        have hY : (0 : ℝ) ≤ ((40000000 * q).choose (7722388 * q) : ℝ) * ((40000000 * q).choose (8451002 * q) : ℝ) * ((8451002 * q).choose (902934 * q) : ℝ) * ((40000000 * q).choose (14889803 * q) : ℝ) * ((14889803 * q).choose (2874621 * q) : ℝ) * (2 : ℝ) ^ (53986869 * q) := by positivity
        have := mul_le_mul_of_nonneg_left hNB (mul_nonneg hX hY)
        rw [div_eq_mul_inv]
        nlinarith
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (by linarith [hterm']); positivity

lemma log_E (α β : ℕ) (h : β < α) (hβ : 0 < β) :
    Real.log (E α β) = α * Real.log α - β * Real.log β - ((α - β : ℕ) : ℝ) * Real.log ((α - β : ℕ) : ℝ) := by
  have h1 : (0 : ℝ) < ((α - β : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt h
  have h2 : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have h3 : (0 : ℝ) < (α : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le β) h)
  unfold E
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  ring

lemma log_nat_split (N k : ℕ) (hN : 0 < N) :
    Real.log (N : ℝ) = k * Real.log 2 + Real.log ((N : ℝ) / 2 ^ k) := by
  rw [Real.log_div (by exact_mod_cast hN.ne') (by positivity), Real.log_pow]; ring

lemma log_902934 : (543608309387982561394735700549 / 1000000000000000000000000000000 : ℝ) ≤ Real.log (902934 : ℝ) - 19 * Real.log 2 ∧ Real.log (902934 : ℝ) - 19 * Real.log 2 ≤ (543608309387982561394763432063 / 1000000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (451467 / 262144 : ℝ)) (by norm_num) 18
  have e := log_nat_split 902934 19 (by norm_num)
  rw [show ((902934 : ℕ) : ℝ) / 2 ^ 19 = (451467 / 262144 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_2874621 : (315340605677957540790266570797 / 1000000000000000000000000000000 : ℝ) ≤ Real.log (2874621 : ℝ) - 21 * Real.log 2 ∧ Real.log (2874621 : ℝ) - 21 * Real.log 2 ≤ (157670302838978770395133285399 / 500000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (2874621 / 2097152 : ℝ)) (by norm_num) 18
  have e := log_nat_split 2874621 21 (by norm_num)
  rw [show ((2874621 : ℕ) : ℝ) / 2 ^ 21 = (2874621 / 2097152 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_7548068 : (587564222120209210797399234749 / 1000000000000000000000000000000 : ℝ) ≤ Real.log (7548068 : ℝ) - 22 * Real.log 2 ∧ Real.log (7548068 : ℝ) - 22 * Real.log 2 ≤ (73445527765026151349728660823 / 125000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (1887017 / 1048576 : ℝ)) (by norm_num) 18
  have e := log_nat_split 7548068 22 (by norm_num)
  rw [show ((7548068 : ℕ) : ℝ) / 2 ^ 22 = (1887017 / 1048576 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_7722388 : (610396228275477459404248863049 / 1000000000000000000000000000000 : ℝ) ≤ Real.log (7722388 : ℝ) - 22 * Real.log 2 ∧ Real.log (7722388 : ℝ) - 22 * Real.log 2 ≤ (610396228275477459405885101753 / 1000000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (1930597 / 1048576 : ℝ)) (by norm_num) 18
  have e := log_nat_split 7722388 22 (by norm_num)
  rw [show ((7722388 : ℕ) : ℝ) / 2 ^ 22 = (1930597 / 1048576 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_8451002 : (7410419306232845971138469671 / 1000000000000000000000000000000 : ℝ) ≤ Real.log (8451002 : ℝ) - 23 * Real.log 2 ∧ Real.log (8451002 : ℝ) - 23 * Real.log 2 ≤ (926302413279105746392308709 / 125000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (4225501 / 4194304 : ℝ)) (by norm_num) 18
  have e := log_nat_split 8451002 23 (by norm_num)
  rw [show ((8451002 : ℕ) : ℝ) / 2 ^ 23 = (4225501 / 4194304 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_12015182 : (89824105472810038326434469763 / 250000000000000000000000000000 : ℝ) ≤ Real.log (12015182 : ℝ) - 23 * Real.log 2 ∧ Real.log (12015182 : ℝ) - 23 * Real.log 2 ≤ (179648210945620076652868939531 / 500000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (6007591 / 4194304 : ℝ)) (by norm_num) 18
  have e := log_nat_split 12015182 23 (by norm_num)
  rw [show ((12015182 : ℕ) : ℝ) / 2 ^ 23 = (6007591 / 4194304 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_14889803 : (143450505334496021735475239593 / 250000000000000000000000000000 : ℝ) ≤ Real.log (14889803 : ℝ) - 23 * Real.log 2 ∧ Real.log (14889803 : ℝ) - 23 * Real.log 2 ≤ (573802021337984086942087841867 / 1000000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (14889803 / 8388608 : ℝ)) (by norm_num) 18
  have e := log_nat_split 14889803 23 (by norm_num)
  rw [show ((14889803 : ℕ) : ℝ) / 2 ^ 23 = (14889803 / 8388608 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_25110197 : (403252243144193195835577735213 / 1000000000000000000000000000000 : ℝ) ≤ Real.log (25110197 : ℝ) - 24 * Real.log 2 ∧ Real.log (25110197 : ℝ) - 24 * Real.log 2 ≤ (403252243144193195835577735849 / 1000000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (25110197 / 16777216 : ℝ)) (by norm_num) 18
  have e := log_nat_split 25110197 24 (by norm_num)
  rw [show ((25110197 : ℕ) : ℝ) / 2 ^ 24 = (25110197 / 16777216 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_25159252 : (40520392618615954974250985763 / 100000000000000000000000000000 : ℝ) ≤ Real.log (25159252 : ℝ) - 24 * Real.log 2 ∧ Real.log (25159252 : ℝ) - 24 * Real.log 2 ≤ (405203926186159549742509858387 / 1000000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (6289813 / 4194304 : ℝ)) (by norm_num) 18
  have e := log_nat_split 25159252 24 (by norm_num)
  rw [show ((25159252 : ℕ) : ℝ) / 2 ^ 24 = (6289813 / 4194304 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_31548998 : (126304010779191547995895905551 / 200000000000000000000000000000 : ℝ) ≤ Real.log (31548998 : ℝ) - 24 * Real.log 2 ∧ Real.log (31548998 : ℝ) - 24 * Real.log 2 ≤ (631520053895957739984845923417 / 1000000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (15774499 / 8388608 : ℝ)) (by norm_num) 18
  have e := log_nat_split 31548998 24 (by norm_num)
  rw [show ((31548998 : ℕ) : ℝ) / 2 ^ 24 = (15774499 / 8388608 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_32277612 : (32717604374784139453106440651 / 50000000000000000000000000000 : ℝ) ≤ Real.log (32277612 : ℝ) - 24 * Real.log 2 ∧ Real.log (32277612 : ℝ) - 24 * Real.log 2 ≤ (654352087495682789080577643647 / 1000000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (8069403 / 4194304 : ℝ)) (by norm_num) 18
  have e := log_nat_split 32277612 24 (by norm_num)
  rw [show ((32277612 : ℕ) : ℝ) / 2 ^ 24 = (8069403 / 4194304 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_40000000 : (43927624519894417882400347313 / 250000000000000000000000000000 : ℝ) ≤ Real.log (40000000 : ℝ) - 25 * Real.log 2 ∧ Real.log (40000000 : ℝ) - 25 * Real.log 2 ≤ (175710498079577671529601389253 / 1000000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (78125 / 65536 : ℝ)) (by norm_num) 18
  have e := log_nat_split 40000000 25 (by norm_num)
  rw [show ((40000000 : ℕ) : ℝ) / 2 ^ 25 = (78125 / 65536 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_80000000 : (43927624519894417882400347313 / 250000000000000000000000000000 : ℝ) ≤ Real.log (80000000 : ℝ) - 26 * Real.log 2 ∧ Real.log (80000000 : ℝ) - 26 * Real.log 2 ≤ (175710498079577671529601389253 / 1000000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (78125 / 65536 : ℝ)) (by norm_num) 18
  have e := log_nat_split 80000000 26 (by norm_num)
  rw [show ((80000000 : ℕ) : ℝ) / 2 ^ 26 = (78125 / 65536 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma log_105159252 : (89831950054273585576626391289 / 200000000000000000000000000000 : ℝ) ≤ Real.log (105159252 : ℝ) - 26 * Real.log 2 ∧ Real.log (105159252 : ℝ) - 26 * Real.log 2 ≤ (17966390010854717115325279489 / 40000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := (26289813 / 16777216 : ℝ)) (by norm_num) 18
  have e := log_nat_split 105159252 26 (by norm_num)
  rw [show ((105159252 : ℕ) : ℝ) / 2 ^ 26 = (26289813 / 16777216 : ℝ) by norm_num] at e
  push_cast at e
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]


lemma log_two_bounds : (3465735902799726547086160607290882840377 / 5000000000000000000000000000000000000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (1732867951399863273543080303645441420189 / 2500000000000000000000000000000000000000 : ℝ) := by
  have h := ZZRec.log_bounds_of_ge_one (r := 2) (by norm_num) 40
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma Rc_pos : 0 < Rc := by
  unfold Rc
  have p0 := E_pos 40000000 7722388 (by norm_num) (by norm_num)
  have p1 := E_pos 40000000 8451002 (by norm_num) (by norm_num)
  have p2 := E_pos 8451002 902934 (by norm_num) (by norm_num)
  have p3 := E_pos 40000000 14889803 (by norm_num) (by norm_num)
  have p4 := E_pos 14889803 2874621 (by norm_num) (by norm_num)
  have p5 := E_pos 105159252 25159252 (by norm_num) (by norm_num)
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos p0 p1) p2) p3) p4) p5) (pow_pos two_pos _)

lemma log_Rc_gt : (10000000 : ℝ) * 17.2114784916916 < Real.log Rc := by
  have p0 := E_pos 40000000 7722388 (by norm_num) (by norm_num)
  have p1 := E_pos 40000000 8451002 (by norm_num) (by norm_num)
  have p2 := E_pos 8451002 902934 (by norm_num) (by norm_num)
  have p3 := E_pos 40000000 14889803 (by norm_num) (by norm_num)
  have p4 := E_pos 14889803 2874621 (by norm_num) (by norm_num)
  have p5 := E_pos 105159252 25159252 (by norm_num) (by norm_num)
  have q1 := mul_pos p0 p1
  have q2 := mul_pos q1 p2
  have q3 := mul_pos q2 p3
  have q4 := mul_pos q3 p4
  have q5 := mul_pos q4 p5
  have h2p : (0 : ℝ) < 2 ^ 53986869 := pow_pos two_pos _
  unfold Rc
  rw [Real.log_mul q5.ne' h2p.ne', Real.log_mul q4.ne' p5.ne', Real.log_mul q3.ne' p4.ne', Real.log_mul q2.ne' p3.ne', Real.log_mul q1.ne' p2.ne', Real.log_mul p0.ne' p1.ne', Real.log_pow]
  rw [log_E 40000000 7722388 (by norm_num) (by norm_num)]
  rw [log_E 40000000 8451002 (by norm_num) (by norm_num)]
  rw [log_E 8451002 902934 (by norm_num) (by norm_num)]
  rw [log_E 40000000 14889803 (by norm_num) (by norm_num)]
  rw [log_E 14889803 2874621 (by norm_num) (by norm_num)]
  rw [log_E 105159252 25159252 (by norm_num) (by norm_num)]
  push_cast
  norm_num only
  have h902934 := log_902934
  have h2874621 := log_2874621
  have h7548068 := log_7548068
  have h7722388 := log_7722388
  have h8451002 := log_8451002
  have h12015182 := log_12015182
  have h14889803 := log_14889803
  have h25110197 := log_25110197
  have h25159252 := log_25159252
  have h31548998 := log_31548998
  have h32277612 := log_32277612
  have h40000000 := log_40000000
  have h80000000 := log_80000000
  have h105159252 := log_105159252
  have h2 := log_two_bounds
  linarith [h902934.1, h902934.2, h2874621.1, h2874621.2, h7548068.1, h7548068.2, h7722388.1, h7722388.2, h8451002.1, h8451002.2, h12015182.1, h12015182.2, h14889803.1, h14889803.2, h25110197.1, h25110197.2, h25159252.1, h25159252.2, h31548998.1, h31548998.2, h32277612.1, h32277612.2, h40000000.1, h40000000.2, h80000000.1, h80000000.2, h105159252.1, h105159252.2, h2.1, h2.2]

end PiIrrationality.ZZEven.CoefGeSharp

open PiIrrationality.ZZEven PiIrrationality.ZZEven.CoefGeSharp in
/-- **Sharp lower rate**: eventually `exp(17.2114784916916 n) ≤ coef n`. -/
theorem PiIrrationality.ZZEven.coef_ge_sharp :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.exp (17.2114784916916 * (n : ℝ)) ≤ (PiIrrationality.ZZEven.coef n : ℝ) := by
  set X : ℝ := Real.exp ((10000000 : ℝ) * 17.2114784916916) with hXdef
  have hX : 0 < X := Real.exp_pos _
  have hRc := Rc_pos
  have hb : 1 < Rc / X := by
    rw [one_lt_div hX, hXdef, ← Real.exp_log hRc]
    exact Real.exp_lt_exp.mpr log_Rc_gt
  set D0 : ℝ := ((40000000 + 1) ^ 3 * (8451002 + 1) * (14889803 + 1) * (105159252 + 1) * (105159252 / 80000000) : ℝ) with hD0
  have hD0pos : 0 < D0 := by rw [hD0]; norm_num
  set c : ℝ := D0 * X with hc
  have hcpos : 0 < c := by positivity
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 6 hb
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / c by positivity))
  obtain ⟨Q0, hQ0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨10000000 * (Q0 + 1), fun n hn => ?_⟩
  set q := n / 10000000 with hqdef
  have hqQ : Q0 + 1 ≤ q := by omega
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hcoef := Rc_pow_le n hq1
  rw [← hqdef] at hcoef
  have hpoly := hQ0 q (by omega)
  have hbq : (0 : ℝ) < (Rc / X) ^ q := by positivity
  have hpoly' : c * (q : ℝ) ^ 6 < (Rc / X) ^ q := by
    rw [div_lt_div_iff₀ hbq hcpos] at hpoly
    linarith
  have hD : ((40000000 * q + 1 : ℕ) : ℝ) ^ 3 * ((8451002 * q + 1 : ℕ) : ℝ) * ((14889803 * q + 1 : ℕ) : ℝ) *
      ((105159252 * q + 1 : ℕ) : ℝ) * (105159252 / 80000000) ≤ D0 * (q : ℝ) ^ 6 := by
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    rw [hD0]
    push_cast
    have a1 : (40000000 * (q : ℝ) + 1) ≤ (40000000 + 1) * q := by linarith
    have a2 : (8451002 * (q : ℝ) + 1) ≤ (8451002 + 1) * q := by linarith
    have a3 : (14889803 * (q : ℝ) + 1) ≤ (14889803 + 1) * q := by linarith
    have a4 : (105159252 * (q : ℝ) + 1) ≤ (105159252 + 1) * q := by linarith
    calc (40000000 * (q : ℝ) + 1) ^ 3 * (8451002 * q + 1) * (14889803 * q + 1) * (105159252 * q + 1) * (105159252 / 80000000)
        ≤ ((40000000 + 1) * q) ^ 3 * ((8451002 + 1) * q) * ((14889803 + 1) * q) * ((105159252 + 1) * q) * (105159252 / 80000000) := by
          gcongr
      _ = (40000000 + 1) ^ 3 * (8451002 + 1) * (14889803 + 1) * (105159252 + 1) * (105159252 / 80000000) * (q : ℝ) ^ 6 := by ring
  have hcoef' : Rc ^ q ≤ D0 * (q : ℝ) ^ 6 * (coef n : ℝ) :=
    hcoef.trans (mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg _))
  have hnM : (n : ℝ) ≤ 10000000 * q + 10000000 := by
    have : n < 10000000 * q + 10000000 := by omega
    exact_mod_cast this.le
  have hexp : Real.exp (17.2114784916916 * n) ≤ X ^ (q + 1) := by
    rw [hXdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have hXq : (0 : ℝ) < X ^ q := by positivity
  have hRq : Rc ^ q = (Rc / X) ^ q * X ^ q := by
    rw [← mul_pow, div_mul_cancel₀ _ hX.ne']
  calc Real.exp (17.2114784916916 * n) ≤ X ^ (q + 1) := hexp
    _ ≤ (coef n : ℝ) := by
        have k1 : X ^ (q + 1) * (D0 * (q : ℝ) ^ 6) ≤ Rc ^ q := by
          rw [hRq, pow_succ]
          have := mul_lt_mul_of_pos_right hpoly' hXq
          rw [hc] at this
          nlinarith
        have hK : (0 : ℝ) < D0 * (q : ℝ) ^ 6 := by positivity
        have := k1.trans hcoef'
        rw [mul_comm (D0 * (q : ℝ) ^ 6) (coef n : ℝ)] at this
        exact le_of_mul_le_mul_right this hK

end

/-! ## Part `PhiSum` -/

section
/-!
# The prime saving: `Σ_{k<K} (4/(2k+1) - 6/(3k+2)) ≥ 1.29055122046966` for `K = 10²⁰`

The tail `Σ_{k≥K} 2/((2k+1)(3k+2))` is bounded below by a telescoping difference `T(k) - T(k+1)`,
where `T` is the asymptotic expansion of the tail to order `(k+1/2)^{-10}`.
-/

namespace PiIrrationality.ZZEven.PhiSum

/-- The telescoping majorant of the tail. -/
noncomputable def T (k : ℝ) : ℝ := (1 / 3 : ℝ) / (k + 1 / 2) ^ 1 + (5 / 36 : ℝ) / (k + 1 / 2) ^ 2 + (5 / 162 : ℝ) / (k + 1 / 2) ^ 3 + (-25 / 2592 : ℝ) / (k + 1 / 2) ^ 4 + (-17 / 1944 : ℝ) / (k + 1 / 2) ^ 5 + (575 / 139968 : ℝ) / (k + 1 / 2) ^ 6 + (455 / 69984 : ℝ) / (k + 1 / 2) ^ 7 + (-28225 / 6718464 : ℝ) / (k + 1 / 2) ^ 8 + (-207913 / 22674816 : ℝ) / (k + 1 / 2) ^ 9 + (458995 / 60466176 : ℝ) / (k + 1 / 2) ^ 10

/-- `T` in the variable `m = k + 1/2`. -/
noncomputable def Tm (m : ℝ) : ℝ := (1 / 3 : ℝ) / m ^ 1 + (5 / 36 : ℝ) / m ^ 2 + (5 / 162 : ℝ) / m ^ 3 + (-25 / 2592 : ℝ) / m ^ 4 + (-17 / 1944 : ℝ) / m ^ 5 + (575 / 139968 : ℝ) / m ^ 6 + (455 / 69984 : ℝ) / m ^ 7 + (-28225 / 6718464 : ℝ) / m ^ 8 + (-207913 / 22674816 : ℝ) / m ^ 9 + (458995 / 60466176 : ℝ) / m ^ 10

lemma T_eq (k : ℝ) : T k = Tm (k + 1 / 2) := rfl

lemma resid (x : ℝ) (hx : 0 ≤ x) :
    T (30 + x) - T (30 + x + 1) ≤ (4 : ℝ) / (2 * (30 + x) + 1) - 6 / (3 * (30 + x) + 2) := by
  set m : ℝ := 30 + x + 1 / 2 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hm1 : m + 1 ≠ 0 := by linarith
  have h6 : 6 * m + 1 ≠ 0 := by linarith
  have hf : (4 : ℝ) / (2 * (30 + x) + 1) - 6 / (3 * (30 + x) + 2) = 2 / (m * (6 * m + 1)) := by
    rw [hm]; field_simp; ring
  have hT : T (30 + x) - T (30 + x + 1) = Tm m - Tm (m + 1) := by
    rw [T_eq, T_eq]; congr 2 <;> rw [hm] <;> ring
  rw [hf, hT]
  have key : 2 / (m * (6 * m + 1)) - (Tm m - Tm (m + 1)) =
      ((-458995 / 60466176 : ℝ) * m ^ 0 + (-2546057 / 22674816 : ℝ) * m ^ 1 + (-58604243 / 90699264 : ℝ) * m ^ 2 + (-58560565 / 30233088 : ℝ) * m ^ 3 + (-190501525 / 60466176 : ℝ) * m ^ 4 + (-62014841 / 30233088 : ℝ) * m ^ 5 + (9483647 / 5038848 : ℝ) * m ^ 6 + (76479299 / 15116544 : ℝ) * m ^ 7 + (255207875 / 60466176 : ℝ) * m ^ 8 + (20824925 / 15116544 : ℝ) * m ^ 9) / (m ^ 10 * (m + 1) ^ 10 * (6 * m + 1)) := by
    unfold Tm
    have := hm0.ne'
    field_simp
    ring
  have hP : 0 ≤ (-458995 / 60466176 : ℝ) * m ^ 0 + (-2546057 / 22674816 : ℝ) * m ^ 1 + (-58604243 / 90699264 : ℝ) * m ^ 2 + (-58560565 / 30233088 : ℝ) * m ^ 3 + (-190501525 / 60466176 : ℝ) * m ^ 4 + (-62014841 / 30233088 : ℝ) * m ^ 5 + (9483647 / 5038848 : ℝ) * m ^ 6 + (76479299 / 15116544 : ℝ) * m ^ 7 + (255207875 / 60466176 : ℝ) * m ^ 8 + (20824925 / 15116544 : ℝ) * m ^ 9 := by
    have e : (-458995 / 60466176 : ℝ) * m ^ 0 + (-2546057 / 22674816 : ℝ) * m ^ 1 + (-58604243 / 90699264 : ℝ) * m ^ 2 + (-58560565 / 30233088 : ℝ) * m ^ 3 + (-190501525 / 60466176 : ℝ) * m ^ 4 + (-62014841 / 30233088 : ℝ) * m ^ 5 + (9483647 / 5038848 : ℝ) * m ^ 6 + (76479299 / 15116544 : ℝ) * m ^ 7 + (255207875 / 60466176 : ℝ) * m ^ 8 + (20824925 / 15116544 : ℝ) * m ^ 9 = (537930056516412927985693 / 15479341056 : ℝ) * x ^ 0 + (117750807200734987739287 / 11609505792 : ℝ) * x ^ 1 + (3818483265559337054723 / 2902376448 : ℝ) * x ^ 2 + (24077215775137159015 / 241864704 : ℝ) * x ^ 3 + (2342288210407066915 / 483729408 : ℝ) * x ^ 4 + (18988308307756103 / 120932352 : ℝ) * x ^ 5 + (68413681101695 / 20155392 : ℝ) * x ^ 6 + (713050072999 / 15116544 : ℝ) * x ^ 7 + (23120975525 / 60466176 : ℝ) * x ^ 8 + (20824925 / 15116544 : ℝ) * x ^ 9 := by rw [hm]; ring
    rw [e]; positivity
  have := div_nonneg hP (by positivity : (0 : ℝ) ≤ m ^ 10 * (m + 1) ^ 10 * (6 * m + 1))
  linarith

/-- Telescoping from `30`. -/
lemma sum_ge (K : ℕ) (hK : 30 ≤ K) :
    (∑ k ∈ Finset.range 30, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) + T 30 - T K ≤
      ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2)) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [Finset.sum_range_succ _ K]
    have h30 : (30 : ℝ) ≤ K := by exact_mod_cast hK
    have h := resid ((K : ℝ) - 30) (by linarith)
    rw [show (30 : ℝ) + ((K : ℝ) - 30) = K by ring] at h
    push_cast
    linarith

lemma S30 : ∑ k ∈ Finset.range 30, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2)) = (3251493511581453008884238362967 / 2541277822022934075399821302800 : ℝ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num

lemma T30 : T 30 = (5600232617691250938011 / 505466227089378656477388 : ℝ) := by unfold T; norm_num

lemma T_big : T ((100000000000000000000 : ℕ) : ℝ) ≤ 1 / 100000000000000000000 := by
  simp only [Nat.cast_ofNat]; unfold T; norm_num

end PiIrrationality.ZZEven.PhiSum

open PiIrrationality.ZZEven.PhiSum in
/-- **The prime saving** up to `K = 10²⁰`. -/
theorem PiIrrationality.ZZEven.phi_sum_ge :
    (1.29055122046966 : ℝ) ≤
      ∑ k ∈ Finset.range 100000000000000000000, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2)) := by
  have h := sum_ge 100000000000000000000 (by norm_num)
  rw [S30, T30] at h
  refine le_trans ?_ h
  have hb := T_big
  generalize T ((100000000000000000000 : ℕ) : ℝ) = t at hb ⊢
  clear h
  norm_num at hb ⊢
  linarith

end

/-! ## Part `Assembly` -/

section
open Filter Real

namespace PiIrrationality.ZZEven.Record

lemma two_pow_eq_exp (k : ℕ) : (2 : ℝ) ^ k = Real.exp (k * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

lemma M_pos (n : ℕ) : 0 < M n := by
  unfold M
  have h1 : (0 : ℝ) < Nat.lcmUpto (8 * n) := by exact_mod_cast Nat.lcmUpto_pos _
  have h2 : (0 : ℝ) < Phi n := by
    unfold Phi
    exact_mod_cast Finset.prod_pos fun p hp => by
      unfold deletedPrimes at hp
      exact (Finset.mem_filter.mp hp).2.1.pos
  positivity

/-- Eventual upper bound for the normalising multiplier. -/
lemma M_le (δ lam : ℝ) (hδ : 0 < δ)
    (hphi : ∀ᶠ n : ℕ in atTop, Real.exp ((lam - δ) * n) ≤ (Phi n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      M n ≤ 16 * Real.exp ((8 + 9 * δ - lam - 5 * Real.log 2) * n) := by
  have hl : ∀ᶠ n : ℕ in atTop,
      (Nat.lcmUpto (8 * n) : ℝ) ≤ Real.exp ((1 + δ) * ((8 * n : ℕ) : ℝ)) :=
    (tendsto_id.const_mul_atTop' (by norm_num : 0 < 8)).eventually
      (PiIrrationality.lcmUpto_le_exp δ hδ)
  filter_upwards [hl, hphi] with n hl hphi
  unfold M
  have hPhi : 0 < (Phi n : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hphi
  rw [div_le_iff₀ (by positivity), two_pow_eq_exp (5 * n)]
  have hsplit : (1 + δ) * ((8 * n : ℕ) : ℝ) = (8 + 9 * δ - lam - 5 * Real.log 2) * n +
      (((5 * n : ℕ) : ℝ) * Real.log 2 + (lam - δ) * n) := by push_cast; ring
  have h16 : (2 : ℝ) ^ 4 = 16 := by norm_num
  calc (2 : ℝ) ^ 4 * (Nat.lcmUpto (8 * n) : ℝ)
      ≤ 16 * Real.exp ((1 + δ) * ((8 * n : ℕ) : ℝ)) := by
        rw [h16]; exact mul_le_mul_of_nonneg_left hl (by norm_num)
    _ = 16 * Real.exp ((8 + 9 * δ - lam - 5 * Real.log 2) * n) *
          (Real.exp ((5 * n : ℕ) * Real.log 2) * Real.exp ((lam - δ) * n)) := by
        rw [hsplit, Real.exp_add, Real.exp_add]; ring
    _ ≤ 16 * Real.exp ((8 + 9 * δ - lam - 5 * Real.log 2) * n) *
          (Real.exp ((5 * n : ℕ) * Real.log 2) * (Phi n : ℝ)) := by
        gcongr

lemma const_le_exp (c δ : ℝ) (hδ : 0 < δ) : ∀ᶠ n : ℕ in atTop, c ≤ Real.exp (δ * n) := by
  have : Tendsto (fun n : ℕ => Real.exp (δ * n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hδ)
  exact this.eventually_ge_atTop c

/-- `log 2` to `10⁻³⁰`. -/
lemma log_two_lo : (0.693147180559945309417232121458 : ℝ) ≤ Real.log 2 := by
  have h := (ZZRec.log_bounds_of_ge_one (r := 2) (by norm_num) 32).1
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

/-- `ρ ≤ exp(-7.0495458479305)`. -/
lemma rho_le : PiIrrationality.ZZEven.SharpIntegral.ρ ≤ Real.exp (-7.0495458479305) := by
  have hr := (ZZRec.log_bounds_of_ge_one (r := 19531250000000000 / 17356059646937919)
    (by norm_num) 18).1
  simp only [ZZRec.lsum, Finset.sum_range_succ, Finset.sum_range_zero] at hr
  norm_num at hr
  have h2 := log_two_lo
  have hρ : PiIrrationality.ZZEven.SharpIntegral.ρ =
      Real.exp (-(10 * Real.log 2 + Real.log (19531250000000000 / 17356059646937919))) := by
    rw [Real.exp_neg, Real.exp_add, ← Real.log_rpow (by norm_num),
      Real.exp_log (by positivity), Real.exp_log (by norm_num)]
    unfold PiIrrationality.ZZEven.SharpIntegral.ρ
    norm_num
  rw [hρ]
  apply Real.exp_le_exp.mpr
  linarith

/-- Upper bound for the prime-saving sum. -/
lemma lam_le_two (K : ℕ) :
    ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2)) ≤ 2 - 2 / (K + 1) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have key : (4 : ℝ) / (2 * K + 1) - 6 / (3 * K + 2) ≤ 2 / (K + 1) - 2 / (K + 1 + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (K : ℝ), mul_nonneg hK (sq_nonneg (K : ℝ)), mul_nonneg hK hK,
        pow_nonneg hK 3, pow_nonneg hK 4]
    push_cast
    linarith

end PiIrrationality.ZZEven.Record

open PiIrrationality.ZZEven PiIrrationality.ZZEven.Record in
/-- **The Zeilberger–Zudilin bound** `μ(π) ≤ 7.103205334138`. -/
theorem solution :
    PiIrrationality.UpperBound (7.103205334138 : ℝ) := by
  set δ : ℝ := 1 / 10 ^ 16 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; norm_num
  have hphi := PiIrrationality.ZZEven.phi_lower 100000000000000000000 δ hδ
  have hlamlo := PiIrrationality.ZZEven.phi_sum_ge
  have hlamhi := lam_le_two 100000000000000000000
  generalize ∑ k ∈ Finset.range 100000000000000000000, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2)) = lam
    at hphi hlamlo hlamhi
  have hlamhi' : lam ≤ 2 := by
    have : (0 : ℝ) ≤ 2 / ((100000000000000000000 : ℕ) + 1 : ℝ) := by positivity
    linarith
  clear hlamhi
  have hL := log_two_lo
  have hL2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  set τ : ℝ := 7.0495458479305 with hτ
  set cu : ℝ := 17.2114784916918 with hcu
  set cl : ℝ := 17.2114784916916 with hcl
  set s : ℝ := cu + 8 + 10 * δ - lam - Real.log 2 with hsdef
  set t : ℝ := τ - 8 - 10 * δ + lam + 5 * Real.log 2 with htdef
  set g : ℝ := τ + 4 * Real.log 2 + cl - δ with hgdef
  have hs : 0 < s := by rw [hsdef, hcu, hδdef]; norm_num; linarith
  have ht : 0 < t := by rw [htdef, hτ, hδdef]; norm_num; linarith
  have hsg : s < g := by rw [hsdef, hgdef, hcu, hcl, hτ, hδdef]; norm_num; linarith
  have hB₁ : 1 + s / t ≤ 7.103205334138 := by
    have : s / t ≤ 7.103205334138 - 1 := by
      rw [div_le_iff₀ ht, hsdef, htdef, hcu, hτ, hδdef]
      norm_num
      linarith
    linarith
  have hB₂ : 1 + s / (g - s) ≤ 7.103205334138 := by
    have hgs : 0 < g - s := by linarith
    have : s / (g - s) ≤ 7.103205334138 - 1 := by
      rw [div_le_iff₀ hgs, hsdef, hgdef, hcu, hcl, hτ, hδdef]
      norm_num
      linarith
    linarith
  -- the linear forms
  have hLF : ∀ n : ℕ, ∃ U V : ℤ, 1 ≤ n →
      (M n : ℂ) * J n = (U : ℂ) + (V : ℂ) * (Real.pi : ℂ) ∧
        (V : ℝ) = -(M n * 16 ^ n * (coef n : ℝ) / 4) := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨U, V, h⟩ := PiIrrationality.ZZEven.linearForm n hn
      exact ⟨U, V, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hn⟩
  choose U V hUV using hLF
  have hΛeq : ∀ n, 1 ≤ n → |(U n : ℝ) + V n * Real.pi| = M n * ‖J n‖ := by
    intro n hn
    have h := (hUV n hn).1
    have : ((((U n : ℝ) + V n * Real.pi : ℝ)) : ℂ) = (M n : ℂ) * J n := by
      rw [h]; push_cast; ring
    have habs : |(U n : ℝ) + V n * Real.pi| = ‖((((U n : ℝ) + V n * Real.pi : ℝ)) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [habs, this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (M_pos n)]
  have hVeq : ∀ n, 1 ≤ n → |(V n : ℝ)| = M n * 16 ^ n * (coef n : ℝ) / 4 := by
    intro n hn
    rw [(hUV n hn).2, abs_neg, abs_of_nonneg (by have := M_pos n; positivity)]
  obtain ⟨N₁, hN₁⟩ := PiIrrationality.ZZEven.coef_ge_sharp
  have hM := M_le δ lam hδ hphi
  have h16 : ∀ n : ℕ, (16 : ℝ) ^ n = Real.exp (4 * Real.log 2 * n) := by
    intro n
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, two_pow_eq_exp]; push_cast; ring_nf
  have hJ : ∀ n : ℕ, ‖J n‖ ≤ 2 * Real.exp (-(τ * n)) := by
    intro n
    refine (PiIrrationality.ZZEven.SharpIntegral.norm_J_le n).trans ?_
    have h := rho_le
    have hρ0 : 0 ≤ PiIrrationality.ZZEven.SharpIntegral.ρ := PiIrrationality.ZZEven.SharpIntegral.ρ_pos.le
    calc 2 * PiIrrationality.ZZEven.SharpIntegral.ρ ^ n ≤ 2 * Real.exp (-7.0495458479305) ^ n := by
          gcongr
      _ = 2 * Real.exp (-(τ * n)) := by
          rw [← Real.exp_nat_mul, hτ]; ring_nf
  apply PiIrrationality.ratio_linearForm_upperBound U V s t g 7.103205334138 hs ht hsg hB₁ hB₂
  · -- coefficient bound
    filter_upwards [hM, eventually_ge_atTop 1, eventually_ge_atTop N₁,
      const_le_exp 4 δ hδ] with n hMn hn hn1 h4
    have hc := hN₁ n hn1
    have hcpos : 0 < (coef n : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hc
    refine ⟨?_, ?_⟩
    · intro h0
      have := hVeq n hn
      rw [h0, Int.cast_zero, abs_zero] at this
      have : 0 < M n * 16 ^ n * (coef n : ℝ) / 4 := by
        have := M_pos n; positivity
      linarith
    · rw [hVeq n hn]
      have hcl := PiIrrationality.ZZEven.coef_le_sharp n
      calc M n * 16 ^ n * (coef n : ℝ) / 4
          ≤ 16 * Real.exp ((8 + 9 * δ - lam - 5 * Real.log 2) * n) *
              Real.exp (4 * Real.log 2 * n) * Real.exp (cu * n) / 4 := by
            rw [h16, hcu]; gcongr
        _ = 4 * Real.exp ((s - δ) * n) := by
            have : (s - δ) * n = (8 + 9 * δ - lam - 5 * Real.log 2) * n +
                4 * Real.log 2 * n + cu * n := by rw [hsdef]; ring
            rw [this, Real.exp_add, Real.exp_add]; ring
        _ ≤ Real.exp (δ * n) * Real.exp ((s - δ) * n) := by gcongr
        _ = Real.exp (s * n) := by rw [← Real.exp_add]; congr 1; ring
  · -- decay of the linear form
    filter_upwards [hM, eventually_ge_atTop 1, const_le_exp 32 δ hδ] with n hMn hn h32
    rw [hΛeq n hn]
    calc M n * ‖J n‖
        ≤ 16 * Real.exp ((8 + 9 * δ - lam - 5 * Real.log 2) * n) *
            (2 * Real.exp (-(τ * n))) := by
          exact mul_le_mul hMn (hJ n) (norm_nonneg _) (by positivity)
      _ = 32 * Real.exp (-(t + δ) * n) := by
          have : -(t + δ) * n = (8 + 9 * δ - lam - 5 * Real.log 2) * n + -(τ * n) := by
            rw [htdef]; ring
          rw [this, Real.exp_add]; ring
      _ ≤ Real.exp (δ * n) * Real.exp (-(t + δ) * n) := by gcongr
      _ = Real.exp (-(t * n)) := by rw [← Real.exp_add]; congr 1; ring
  · -- the normalisation-free ratio
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop N₁,
      const_le_exp 8 δ hδ] with n hn hn1 h8
    rw [hΛeq n hn, hVeq n hn]
    have hc := hN₁ n hn1
    have hMp := M_pos n
    have key : ‖J n‖ ≤ Real.exp (-(g * n)) * (16 ^ n * (coef n : ℝ) / 4) := by
      calc ‖J n‖ ≤ 2 * Real.exp (-(τ * n)) := hJ n
        _ = 8 * Real.exp (-(g + δ) * n) *
              (Real.exp (4 * Real.log 2 * n) * Real.exp (cl * n) / 4) := by
            have : -(τ * n) = -(g + δ) * n + 4 * Real.log 2 * n + cl * n := by
              rw [hgdef]; ring
            rw [this, Real.exp_add, Real.exp_add]; ring
        _ ≤ Real.exp (δ * n) * Real.exp (-(g + δ) * n) *
              (Real.exp (4 * Real.log 2 * n) * (coef n : ℝ) / 4) := by
            rw [hcl]; gcongr
        _ = Real.exp (-(g * n)) * (16 ^ n * (coef n : ℝ) / 4) := by
            rw [h16 n]
            have : -(g * n) = δ * n + -(g + δ) * n := by ring
            rw [this, Real.exp_add]
    calc M n * ‖J n‖ ≤ M n * (Real.exp (-(g * n)) * (16 ^ n * (coef n : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left key hMp.le
      _ = Real.exp (-(g * n)) * (M n * 16 ^ n * (coef n : ℝ) / 4) := by ring

end
