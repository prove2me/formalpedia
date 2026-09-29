-- Prove2me | solution 1 for WorkbookSource.base_30023
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:49:57.310051+00:00
-- url     : https://prove2.me/submissions/32541421-5cca-4db7-9dd5-dd6dc5fa8101

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + 2 * b + 3 * c + 4 * d) / (5 * a + 6 * b + 7 * c + 8 * d) + (2 * a + 3 * b + 4 * c + d) / (6 * a + 7 * b + 8 * c + 5 * d) + (3 * a + 4 * b + c + 2 * d) / (7 * a + 8 * b + 5 * c + 6 * d) + (4 * a + b + 2 * c + 3 * d) / (8 * a + 5 * b + 6 * c + 7 * d) ≤ 20 / 13  := by
  have hn : 0 ≤ (1672*a^4 + 3304*a^3*b + 1472*a^3*c + 2056*a^3*d + 2112*a^2*b^2 - 2024*a^2*b*c - 1504*a^2*b*d - 912*a^2*c^2 - 3272*a^2*c*d + 2112*a^2*d^2 + 2056*a*b^3 - 1504*a*b^2*c - 3272*a*b^2*d - 3272*a*b*c^2 - 13440*a*b*c*d - 2024*a*b*d^2 + 1472*a*c^3 - 2024*a*c^2*d - 1504*a*c*d^2 + 3304*a*d^3 + 1672*b^4 + 3304*b^3*c + 1472*b^3*d + 2112*b^2*c^2 - 2024*b^2*c*d - 912*b^2*d^2 + 2056*b*c^3 - 1504*b*c^2*d - 3272*b*c*d^2 + 1472*b*d^3 + 1672*c^4 + 3304*c^3*d + 2112*c^2*d^2 + 2056*c*d^3 + 1672*d^4) := by
    have hs0 : 0 ≤ (25120/9 : ℝ) * (1) * (-122447*a^2/251200 - 748*a*b/785 + 26073*a*c/251200 - 37*a*d/1570 - 118433*b^2/251200 - 37*b*c/1570 - 26073*b*d/251200 + 3713*c^2/6280 + c*d + 2309*d^2/6280)^2 := by positivity
    have hs1 : 0 ≤ (6569416/2355 : ℝ) * (1) * (-190470349*a^2/394164960 - 74*a*b/1607 - 26073*a*c/257120 - 1533*a*d/1607 + 76264793*b^2/131388320 + b*c + 26073*b*d/257120 + 3762511*c^2/9854124 - 6294149*d^2/13138832)^2 := by positivity
    have hs2 : 0 ≤ (1652312919/1285600 : ℝ) * (1) * (-289912493*a^2/550770973 - 236858720*a*b/550770973 - a*c + 236858720*a*d/550770973 + 954483559*b^2/3304625838 + b*d - 260858480*c^2/550770973 + 2350142279*d^2/3304625838)^2 := by positivity
    have hs3 : 0 ≤ (21973376096/1652312919 : ℝ) * (1) * (-10029*a^2/163520 - a*b + a*d - 3011*b^2/6132 + 10029*c^2/163520 + 3011*d^2/6132)^2 := by positivity
    have hs4 : 0 ≤ (56532431/44150400 : ℝ) * (1) * (-b^2 + d^2)^2 := by positivity
    have hs5 : 0 ≤ (56532431/44150400 : ℝ) * (1) * (-a^2 + c^2)^2 := by positivity
    have hs6 : 0 ≤ (128/9 : ℝ) * (c*d) * (-a + b - c/2 + d/2)^2 := by positivity
    have hs7 : 0 ≤ (128 : ℝ) * (b*d) * (-b + d)^2 := by positivity
    have hs8 : 0 ≤ (128/9 : ℝ) * (b*c) * (-a + b/2 - c/2 + d)^2 := by positivity
    have hs9 : 0 ≤ (128/9 : ℝ) * (a*d) * (a/2 - b + c - d/2)^2 := by positivity
    have hs10 : 0 ≤ (128 : ℝ) * (a*c) * (-a + c)^2 := by positivity
    have hs11 : 0 ≤ (128/9 : ℝ) * (a*b) * (-a/2 + b/2 - c + d)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11]
  have hd : (0 : ℝ) < (13*(5*a + 6*b + 7*c + 8*d)*(6*a + 7*b + 8*c + 5*d)*(7*a + 8*b + 5*c + 6*d)*(8*a + 5*b + 6*c + 7*d)) := by positivity
  have heqrat : ( 20 / 13  ) - ( (a + 2 * b + 3 * c + 4 * d) / (5 * a + 6 * b + 7 * c + 8 * d) + (2 * a + 3 * b + 4 * c + d) / (6 * a + 7 * b + 8 * c + 5 * d) + (3 * a + 4 * b + c + 2 * d) / (7 * a + 8 * b + 5 * c + 6 * d) + (4 * a + b + 2 * c + 3 * d) / (8 * a + 5 * b + 6 * c + 7 * d) ) = (1672*a^4 + 3304*a^3*b + 1472*a^3*c + 2056*a^3*d + 2112*a^2*b^2 - 2024*a^2*b*c - 1504*a^2*b*d - 912*a^2*c^2 - 3272*a^2*c*d + 2112*a^2*d^2 + 2056*a*b^3 - 1504*a*b^2*c - 3272*a*b^2*d - 3272*a*b*c^2 - 13440*a*b*c*d - 2024*a*b*d^2 + 1472*a*c^3 - 2024*a*c^2*d - 1504*a*c*d^2 + 3304*a*d^3 + 1672*b^4 + 3304*b^3*c + 1472*b^3*d + 2112*b^2*c^2 - 2024*b^2*c*d - 912*b^2*d^2 + 2056*b*c^3 - 1504*b*c^2*d - 3272*b*c*d^2 + 1472*b*d^3 + 1672*c^4 + 3304*c^3*d + 2112*c^2*d^2 + 2056*c*d^3 + 1672*d^4) / (13*(5*a + 6*b + 7*c + 8*d)*(6*a + 7*b + 8*c + 5*d)*(7*a + 8*b + 5*c + 6*d)*(8*a + 5*b + 6*c + 7*d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a + 2 * b + 3 * c + 4 * d) / (5 * a + 6 * b + 7 * c + 8 * d) + (2 * a + 3 * b + 4 * c + d) / (6 * a + 7 * b + 8 * c + 5 * d) + (3 * a + 4 * b + c + 2 * d) / (7 * a + 8 * b + 5 * c + 6 * d) + (4 * a + b + 2 * c + 3 * d) / (8 * a + 5 * b + 6 * c + 7 * d) ≤ 20 / 13) := @solution
#print axioms solution
