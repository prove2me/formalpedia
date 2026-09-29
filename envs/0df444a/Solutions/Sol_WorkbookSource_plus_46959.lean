-- Prove2me | solution 1 for WorkbookSource.plus_46959
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:31:48.159882+00:00
-- url     : https://prove2.me/submissions/d5508ff7-ea46-4b82-830a-2c4ac757bc99

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c p q r : ℝ) (hp : 3 * (1 + r) ≥ p ^ 2 + p * q + q ^ 2) : a ^ 4 + b ^ 4 + c ^ 4 + r * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + (p + q - r - 1) * (a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2) ≥ p * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + q * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3)   := by
  have hw0 : 0 ≤ (-p^2 - p*q - q^2 + 3*r + 3) := by linarith only [hp]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (-a^2/2 + a*b*p/2 + a*b*q/2 - a*c*p/2 - b^2/2 - b*c*q/2 + c^2)^2 + (3/4 : ℝ) * (1) * (-a^2 + a*b*p/3 - a*b*q/3 + a*c*p/3 + 2*a*c*q/3 + b^2 - 2*b*c*p/3 - b*c*q/3)^2 + (1/3 : ℝ) * ((-p^2 - p*q - q^2 + 3*r + 3)) * (-a*b/2 - a*c/2 + b*c)^2 + (1/4 : ℝ) * ((-p^2 - p*q - q^2 + 3*r + 3)) * (-a*b + a*c)^2 := by positivity
  have hid : ( a ^ 4 + b ^ 4 + c ^ 4 + r * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + (p + q - r - 1) * (a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2) ) - ( p * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + q * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3)   ) = (1 : ℝ) * (1) * (-a^2/2 + a*b*p/2 + a*b*q/2 - a*c*p/2 - b^2/2 - b*c*q/2 + c^2)^2 + (3/4 : ℝ) * (1) * (-a^2 + a*b*p/3 - a*b*q/3 + a*c*p/3 + 2*a*c*q/3 + b^2 - 2*b*c*p/3 - b*c*q/3)^2 + (1/3 : ℝ) * ((-p^2 - p*q - q^2 + 3*r + 3)) * (-a*b/2 - a*c/2 + b*c)^2 + (1/4 : ℝ) * ((-p^2 - p*q - q^2 + 3*r + 3)) * (-a*b + a*c)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c p q r : ℝ) (hp : 3 * (1 + r) ≥ p ^ 2 + p * q + q ^ 2), a ^ 4 + b ^ 4 + c ^ 4 + r * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + (p + q - r - 1) * (a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2) ≥ p * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + q * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3)) := @solution
#print axioms solution
