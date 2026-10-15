-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_signs_from_real_grid
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T09:12:33.236592+00:00
-- url     : https://prove2.me/submissions/5b6addea-a7e1-4528-b713-44bc089e915d

import Definitions.Def_TaoFivePrimes_RHHighCoefficientFunctions
import Definitions.Def_TaoFivePrimes_RHHighHeightBracketInterface
import Theorems.Thm_TaoFivePrimes_rh_high_height_real_grid_sign_checks
namespace RHHighSignsFromRealGrid
namespace RHHighBinningSemantic
export _root_.RHHighBinningSemantic (accumulate_value add_get add_length bins_value coefficientAt coefficientAt_add pairValue sparseValue sparseValue_cons termsAux_iterates termsAux_length terms_length)
end RHHighBinningSemantic
namespace RHHighDirichletArithmetic
export _root_.RHHighDirichletArithmetic (bin coefficient compute delta exponent guard logInput loga power)
end RHHighDirichletArithmetic
namespace RHHighDirichletBinning
export _root_.RHHighDirichletBinning (accumulate add bin bins decode decodeCoefficients field terms termsAux)
end RHHighDirichletBinning
namespace RHHighFullCoefficient
export _root_.RHHighFullCoefficient (F L W delta group weight)
end RHHighFullCoefficient
namespace RHHighGammaArithmetic
export _root_.RHHighGammaArithmetic (Frac P Record add compute log2pi phaseCS round square sum)
end RHHighGammaArithmetic
namespace RHHighGammaGuards
export _root_.RHHighGammaGuards (guard)
end RHHighGammaGuards
namespace RHHighGenericExpHorner
export _root_.RHHighGenericExpHorner (cn cp horner sn sp)
end RHHighGenericExpHorner
namespace RHHighGlobalBinTree
export _root_.RHHighGlobalBinTree (flatten get get_sound length_flatten size valid zeroWord)
end RHHighGlobalBinTree
namespace RHHighGlobalDirichletBins
export _root_.RHHighGlobalDirichletBins (coefficient coefficient_bound coefficients_checked flatten_checked groups tree valid_checked values word word_eq)
end RHHighGlobalDirichletBins
namespace RHHighGlobalDirichletBins00
export _root_.RHHighGlobalDirichletBins00 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHHighGlobalDirichletBins00
namespace RHHighGlobalDirichletBins01
export _root_.RHHighGlobalDirichletBins01 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHHighGlobalDirichletBins01
namespace RHHighGlobalDirichletBins02
export _root_.RHHighGlobalDirichletBins02 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHHighGlobalDirichletBins02
namespace RHHighGlobalDirichletBins03
export _root_.RHHighGlobalDirichletBins03 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 rows)
end RHHighGlobalDirichletBins03
namespace RHHighHeight
export _root_.RHHighHeight (critical normalized normalizedComplex windowZeros)
end RHHighHeight
namespace RHHighHeightBracketData
export _root_.RHHighHeightBracketData (Bracket certificate leaf0 leaf1 leaf10 leaf100 leaf101 leaf102 leaf103 leaf104 leaf105 leaf106 leaf107 leaf108 leaf109 leaf11 leaf110 leaf111 leaf112 leaf113 leaf114 leaf115 leaf116 leaf117 leaf118 leaf119 leaf12 leaf120 leaf121 leaf122 leaf123 leaf124 leaf125 leaf126 leaf127 leaf128 leaf129 leaf13 leaf130 leaf131 leaf132 leaf133 leaf134 leaf135 leaf136 leaf137 leaf138 leaf139 leaf14 leaf140 leaf141 leaf142 leaf143 leaf144 leaf145 leaf146 leaf147 leaf148 leaf149 leaf15 leaf150 leaf151 leaf152 leaf153 leaf154 leaf155 leaf156 leaf157 leaf158 leaf159 leaf16 leaf160 leaf161 leaf162 leaf163 leaf164 leaf165 leaf166 leaf167 leaf168 leaf169 leaf17 leaf170 leaf171 leaf172 leaf173 leaf174 leaf175 leaf176 leaf177 leaf178 leaf179 leaf18 leaf180 leaf181 leaf182 leaf183 leaf184 leaf185 leaf186 leaf187 leaf188 leaf189 leaf19 leaf190 leaf191 leaf192 leaf193 leaf194 leaf195 leaf196 leaf197 leaf198 leaf199 leaf2 leaf20 leaf200 leaf201 leaf202 leaf203 leaf204 leaf205 leaf206 leaf207 leaf208 leaf209 leaf21 leaf210 leaf211 leaf212 leaf213 leaf214 leaf215 leaf216 leaf217 leaf218 leaf219 leaf22 leaf220 leaf221 leaf222 leaf223 leaf224 leaf225 leaf226 leaf227 leaf228 leaf229 leaf23 leaf230 leaf231 leaf232 leaf233 leaf234 leaf235 leaf236 leaf237 leaf238 leaf239 leaf24 leaf240 leaf241 leaf242 leaf243 leaf244 leaf245 leaf246 leaf247 leaf248 leaf249 leaf25 leaf250 leaf251 leaf252 leaf253 leaf254 leaf255 leaf256 leaf257 leaf258 leaf259 leaf26 leaf260 leaf261 leaf262 leaf263 leaf264 leaf265 leaf266 leaf267 leaf268 leaf269 leaf27 leaf270 leaf271 leaf272 leaf273 leaf274 leaf275 leaf276 leaf277 leaf278 leaf279 leaf28 leaf280 leaf281 leaf282 leaf283 leaf284 leaf285 leaf286 leaf287 leaf288 leaf289 leaf29 leaf290 leaf291 leaf292 leaf293 leaf294 leaf295 leaf296 leaf297 leaf298 leaf299 leaf3 leaf30 leaf300 leaf301 leaf302 leaf303 leaf304 leaf305 leaf306 leaf307 leaf308 leaf309 leaf31 leaf310 leaf311 leaf312 leaf313 leaf314 leaf315 leaf316 leaf317 leaf318 leaf319 leaf32 leaf320 leaf321 leaf322 leaf323 leaf324 leaf325 leaf326 leaf327 leaf328 leaf329 leaf33 leaf330 leaf331 leaf332 leaf333 leaf334 leaf335 leaf336 leaf337 leaf338 leaf339 leaf34 leaf340 leaf341 leaf342 leaf343 leaf344 leaf345 leaf346 leaf347 leaf348 leaf349 leaf35 leaf350 leaf351 leaf352 leaf353 leaf354 leaf355 leaf356 leaf357 leaf358 leaf359 leaf36 leaf360 leaf361 leaf362 leaf363 leaf364 leaf365 leaf366 leaf367 leaf368 leaf369 leaf37 leaf370 leaf371 leaf372 leaf373 leaf374 leaf375 leaf376 leaf377 leaf378 leaf379 leaf38 leaf380 leaf381 leaf382 leaf383 leaf384 leaf385 leaf386 leaf387 leaf388 leaf389 leaf39 leaf390 leaf391 leaf392 leaf393 leaf394 leaf395 leaf396 leaf397 leaf398 leaf399 leaf4 leaf40 leaf400 leaf401 leaf402 leaf403 leaf404 leaf405 leaf406 leaf407 leaf408 leaf41 leaf42 leaf43 leaf44 leaf45 leaf46 leaf47 leaf48 leaf49 leaf5 leaf50 leaf51 leaf52 leaf53 leaf54 leaf55 leaf56 leaf57 leaf58 leaf59 leaf6 leaf60 leaf61 leaf62 leaf63 leaf64 leaf65 leaf66 leaf67 leaf68 leaf69 leaf7 leaf70 leaf71 leaf72 leaf73 leaf74 leaf75 leaf76 leaf77 leaf78 leaf79 leaf8 leaf80 leaf81 leaf82 leaf83 leaf84 leaf85 leaf86 leaf87 leaf88 leaf89 leaf9 leaf90 leaf91 leaf92 leaf93 leaf94 leaf95 leaf96 leaf97 leaf98 leaf99 node0 node1 node10 node100 node101 node102 node103 node104 node105 node106 node107 node108 node109 node11 node110 node111 node112 node113 node114 node115 node116 node117 node118 node119 node12 node120 node121 node122 node123 node124 node125 node126 node127 node128 node129 node13 node130 node131 node132 node133 node134 node135 node136 node137 node138 node139 node14 node140 node141 node142 node143 node144 node145 node146 node147 node148 node149 node15 node150 node151 node152 node153 node154 node155 node156 node157 node158 node159 node16 node160 node161 node162 node163 node164 node165 node166 node167 node168 node169 node17 node170 node171 node172 node173 node174 node175 node176 node177 node178 node179 node18 node180 node181 node182 node183 node184 node185 node186 node187 node188 node189 node19 node190 node191 node192 node193 node194 node195 node196 node197 node198 node199 node2 node20 node200 node201 node202 node203 node204 node205 node206 node207 node208 node209 node21 node210 node211 node212 node213 node214 node215 node216 node217 node218 node219 node22 node220 node221 node222 node223 node224 node225 node226 node227 node228 node229 node23 node230 node231 node232 node233 node234 node235 node236 node237 node238 node239 node24 node240 node241 node242 node243 node244 node245 node246 node247 node248 node249 node25 node250 node251 node252 node253 node254 node255 node256 node257 node258 node259 node26 node260 node261 node262 node263 node264 node265 node266 node267 node268 node269 node27 node270 node271 node272 node273 node274 node275 node276 node277 node278 node279 node28 node280 node281 node282 node283 node284 node285 node286 node287 node288 node289 node29 node290 node291 node292 node293 node294 node295 node296 node297 node298 node299 node3 node30 node300 node301 node302 node303 node304 node305 node306 node307 node308 node309 node31 node310 node311 node312 node313 node314 node315 node316 node317 node318 node319 node32 node320 node321 node322 node323 node324 node325 node326 node327 node328 node329 node33 node330 node331 node332 node333 node334 node335 node336 node337 node338 node339 node34 node340 node341 node342 node343 node344 node345 node346 node347 node348 node349 node35 node350 node351 node352 node353 node354 node355 node356 node357 node358 node359 node36 node360 node361 node362 node363 node364 node365 node366 node367 node368 node369 node37 node370 node371 node372 node373 node374 node375 node376 node377 node378 node379 node38 node380 node381 node382 node383 node384 node385 node386 node387 node388 node389 node39 node390 node391 node392 node393 node394 node395 node396 node397 node398 node399 node4 node40 node400 node401 node402 node403 node404 node405 node406 node407 node41 node42 node43 node44 node45 node46 node47 node48 node49 node5 node50 node51 node52 node53 node54 node55 node56 node57 node58 node59 node6 node60 node61 node62 node63 node64 node65 node66 node67 node68 node69 node7 node70 node71 node72 node73 node74 node75 node76 node77 node78 node79 node8 node80 node81 node82 node83 node84 node85 node86 node87 node88 node89 node9 node90 node91 node92 node93 node94 node95 node96 node97 node98 node99)
end RHHighHeightBracketData
namespace RHHighHeightBracketInterface
export _root_.RHHighHeightBracketInterface (leaves point proposalContains scale)
end RHHighHeightBracketInterface
namespace RHHighHomogeneousHorner
export _root_.RHHighHomogeneousHorner (hom)
end RHHighHomogeneousHorner
namespace RHHighLogData
export _root_.RHHighLogData (D F coefficients denominator log2 log2pi numerator rounded)
end RHHighLogData
namespace RHHighNegativeExp
export _root_.RHHighNegativeExp (denominator en ep numerator seed)
end RHHighNegativeExp
namespace RHHighSamplingFunctions
export _root_.RHHighSamplingFunctions (chirpedSample gammaWindow moment sampleIndex sampleTime)
end RHHighSamplingFunctions
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighRealSigns
noncomputable def x (i : Nat) : ℝ := -64+(i:ℝ)/32
noncomputable def proposed (i : Nat) : ℝ := (RHHighRealGrid.value i:ℝ)/(2:ℝ)^80
lemma stable_opposite (a b u v : ℝ)
 (ha:1/10^8≤|a|) (hb:1/10^8≤|b|) (hab:a*b<0)
 (hu:|u-a|≤1/10^9) (hv:|v-b|≤1/10^9) : u*v<0 := by
 have hu':=abs_le.mp hu
 have hv':=abs_le.mp hv
 rcases mul_neg_iff.mp hab with ⟨ha0,hb0⟩|⟨ha0,hb0⟩
 · rw[abs_of_pos ha0] at ha
   rw[abs_of_neg hb0] at hb
   exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
 · rw[abs_of_neg ha0] at ha
   rw[abs_of_pos hb0] at hb
   exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
lemma W_real (u : ℝ) :
 (RHHighFullCoefficient.W u).re=RHHighHeight.normalized (u+3289999936)*Real.exp (-u^2/800) := by
 unfold RHHighFullCoefficient.W RHHighHeight.normalized RHHighHeight.normalizedComplex RHHighHeight.critical
 simp only[←Complex.ofReal_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
 rw[show -u^2/800=-(u^2/800) by ring,Real.exp_sub,Real.exp_neg]
 ring
lemma signs
 (hgrid:∀i:Nat,i<4096 → |(RHHighFullCoefficient.W (x i)).re-proposed i|≤1/10^9) :
 ∀p∈RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate,
 RHHighHeight.normalized (RHHighHeightBracketInterface.point p.l)*
 RHHighHeight.normalized (RHHighHeightBracketInterface.point p.r)<0 := by
 intro p hp
 have h:=(List.all_eq_true.mp TaoFivePrimes.rh_high_height_real_grid_sign_checks) p hp
 simp only[decide_eq_true_eq] at h
 obtain ⟨hl,hr,hml,hmr,hs⟩:=h
 have margin (i : Nat) (hi:2^80≤10^8*(RHHighRealGrid.value i).natAbs) : 1/10^8≤|proposed i| := by
  have ht:(2:ℝ)^80≤10^8*|(RHHighRealGrid.value i:ℝ)| := by
   have h0:((2^80:Nat):ℝ)≤((10^8:Nat):ℝ)*((RHHighRealGrid.value i).natAbs:ℝ):=by exact_mod_cast hi
   simpa only[Nat.cast_pow,Nat.cast_ofNat,Nat.cast_natAbs,Int.cast_abs] using h0
  dsimp only[proposed]
  rw[abs_div,abs_of_pos (by positivity : (0:ℝ)<2^80)]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2^80)).mpr
  linarith
 have hsign:proposed p.l*proposed p.r<0 := by
  dsimp only[proposed]
  rw[div_mul_div_comm]
  exact div_neg_of_neg_of_pos (by exact_mod_cast hs) (by positivity)
 have hv:=stable_opposite _ _ _ _ (margin p.l hml) (margin p.r hmr) hsign (hgrid p.l hl) (hgrid p.r hr)
 have point (i : Nat) : x i+3289999936=RHHighHeightBracketInterface.point i := by
  unfold x RHHighHeightBracketInterface.point
  ring
 rw[W_real,W_real,point,point] at hv
 have he:0< Real.exp (-(x p.l)^2/800)*Real.exp (-(x p.r)^2/800):=by positivity
 have hh:(RHHighHeight.normalized (RHHighHeightBracketInterface.point p.l)*
  RHHighHeight.normalized (RHHighHeightBracketInterface.point p.r))*
  (Real.exp (-(x p.l)^2/800)*Real.exp (-(x p.r)^2/800))<0 := by nlinarith only[hv]
 by_contra! hn
 exact (not_lt_of_ge (mul_nonneg hn he.le)) hh
end RHHighRealSigns
end
end RHHighSignsFromRealGrid
theorem solution
 (hgrid:∀i:Nat,i<4096 →
 |(RHHighFullCoefficient.W (-64+(i:ℝ)/32)).re-(RHHighRealGrid.value i:ℝ)/(2:ℝ)^80|≤1/10^9) :
 ∀p∈RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate,
 RHHighHeight.normalized (RHHighHeightBracketInterface.point p.l)*RHHighHeight.normalized (RHHighHeightBracketInterface.point p.r)<0 := by
 exact RHHighSignsFromRealGrid.RHHighRealSigns.signs hgrid
