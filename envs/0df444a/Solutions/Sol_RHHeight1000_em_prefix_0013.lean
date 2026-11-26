-- Prove2me | solution 1 for RHHeight1000.em_prefix_0013
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:47:16.358865+00:00
-- url     : https://prove2.me/submissions/f4c75a41-6b63-4259-a31c-9f0717b246bc

import Theorems.Thm_RHHeight1000_em_main_0001_0001

import Theorems.Thm_RHHeight1000_em_main_0002_0002

import Theorems.Thm_RHHeight1000_em_main_0003_0003

import Theorems.Thm_RHHeight1000_em_main_0004_0004

import Theorems.Thm_RHHeight1000_em_main_0005_0005

import Theorems.Thm_RHHeight1000_em_main_0006_0006

import Theorems.Thm_RHHeight1000_em_main_0007_0007

import Theorems.Thm_RHHeight1000_em_main_0008_0008

import Theorems.Thm_RHHeight1000_em_main_0009_0009

import Theorems.Thm_RHHeight1000_em_main_0010_0010

import Theorems.Thm_RHHeight1000_em_main_0011_0011

import Theorems.Thm_RHHeight1000_em_main_0012_0012

import Theorems.Thm_RHHeight1000_em_main_0013_0013

/- Interval fold from Salvatore Mercuri and Bhavik Mehta, Apache 2.0. -/

open Zeta.Certificates

namespace Zeta.Certificates

theorem BatchSpec.joinEMGroup001to013 {n₁ an ad bn bd n₂ cn cd en ed : ℕ} (h₁ : BatchSpec n₁ an ad bn bd)
    (h₂ : BatchSpec n₂ cn cd en ed) (hbd : Nat.ble 1 bd = true) (hcd : Nat.ble 1 cd = true)
    (hseam : Nat.ble (bn.mul cd) (cn.mul bd) = true) : BatchSpec (n₁ + n₂) an ad en ed := by
  obtain ⟨C, hCl, hCh, hCt⟩ := h₁
  obtain ⟨D, hDl, hDh, hDt⟩ := h₂
  have hC : C.intervals ≠ [] := by intro he; rw [he] at hCh; simp at hCh
  have hD : D.intervals ≠ [] := by intro he; rw [he] at hDh; simp at hDh
  refine ⟨C.append D (separated_of_endpoints hCt hDh
    (Enclosure.dec_le_dec bn bd cn cd rfl rfl hbd hcd hseam)), ?_, ?_, ?_⟩
  · simp [hCl, hDl]
  · rw [CertifiedZeroIntervals.append_intervals, List.head?_append_of_ne_nil _ hC, hCh]
  · rw [CertifiedZeroIntervals.append_intervals, List.getLast?_append_of_ne_nil _ hD, hDt]



end Zeta.Certificates

namespace EMGroup001to013

theorem part1 : Zeta.Certificates.BatchSpec 1 1000 1000 17846 1000 := RHHeight1000.em_main_0001_0001

theorem part2 : Zeta.Certificates.BatchSpec 2 1000 1000 23170 1000 := BatchSpec.joinEMGroup001to013 part1 RHHeight1000.em_main_0002_0002 rfl rfl rfl

theorem part3 : Zeta.Certificates.BatchSpec 3 1000 1000 27670 1000 := BatchSpec.joinEMGroup001to013 part2 RHHeight1000.em_main_0003_0003 rfl rfl rfl

theorem part4 : Zeta.Certificates.BatchSpec 4 1000 1000 31718 1000 := BatchSpec.joinEMGroup001to013 part3 RHHeight1000.em_main_0004_0004 rfl rfl rfl

theorem part5 : Zeta.Certificates.BatchSpec 5 1000 1000 35467 1000 := BatchSpec.joinEMGroup001to013 part4 RHHeight1000.em_main_0005_0005 rfl rfl rfl

theorem part6 : Zeta.Certificates.BatchSpec 6 1000 1000 38999 1000 := BatchSpec.joinEMGroup001to013 part5 RHHeight1000.em_main_0006_0006 rfl rfl rfl

theorem part7 : Zeta.Certificates.BatchSpec 7 1000 1000 42364 1000 := BatchSpec.joinEMGroup001to013 part6 RHHeight1000.em_main_0007_0007 rfl rfl rfl

theorem part8 : Zeta.Certificates.BatchSpec 8 1000 1000 45593 1000 := BatchSpec.joinEMGroup001to013 part7 RHHeight1000.em_main_0008_0008 rfl rfl rfl

theorem part9 : Zeta.Certificates.BatchSpec 9 1000 1000 48711 1000 := BatchSpec.joinEMGroup001to013 part8 RHHeight1000.em_main_0009_0009 rfl rfl rfl

theorem part10 : Zeta.Certificates.BatchSpec 10 1000 1000 51734 1000 := BatchSpec.joinEMGroup001to013 part9 RHHeight1000.em_main_0010_0010 rfl rfl rfl

theorem part11 : Zeta.Certificates.BatchSpec 11 1000 1000 54675 1000 := BatchSpec.joinEMGroup001to013 part10 RHHeight1000.em_main_0011_0011 rfl rfl rfl

theorem part12 : Zeta.Certificates.BatchSpec 12 1000 1000 57545 1000 := BatchSpec.joinEMGroup001to013 part11 RHHeight1000.em_main_0012_0012 rfl rfl rfl

theorem part13 : Zeta.Certificates.BatchSpec 13 1000 1000 60352 1000 := BatchSpec.joinEMGroup001to013 part12 RHHeight1000.em_main_0013_0013 rfl rfl rfl

end EMGroup001to013

theorem solution : Zeta.Certificates.BatchSpec 13 1000 1000 60352 1000 := EMGroup001to013.part13

#print axioms solution
