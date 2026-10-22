-- Prove2me | solution 1 for OffloadGNEP.Ext.pairE_Fe_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:49:26.721702+00:00
-- url     : https://prove2.me/submissions/0a1c3794-6c4a-469d-9f6d-d0817f086a61

import Mathlib
import Definitions.Def_OffloadGNEP_Ext_Setting

set_option autoImplicit false
open OffloadGNEP.Ext

lemma og_sumT (f : OffloadGNEP.Exist.Tier → ℝ) :
    ∑ i, f i = f .m + f .clet + f .cloud := by
  show ∑ i ∈ ({OffloadGNEP.Exist.Tier.m, OffloadGNEP.Exist.Tier.clet,
    OffloadGNEP.Exist.Tier.cloud} : Finset OffloadGNEP.Exist.Tier), f i = _
  rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  ring

theorem solution {N : ℕ} (P : Params N)
    (x y : Fin N → OffloadGNEP.Exist.Tier → ℝ) (ρ σ : ℝ) :
    pairE (Fe P (y, σ) - Fe P (x, ρ)) ((y, σ) - (x, ρ)) =
      OffloadGNEP.Exist.pair (F P y - F P x) (y - x) := by
  have hu : ∀ u : Fin N,
      ∑ i, ((F P y u i + price P σ u i) - (F P x u i + price P ρ u i)) * (y u i - x u i) =
        ∑ i, (F P y u i - F P x u i) * (y u i - x u i) +
          (σ - ρ) * (P.delta u / (P.n : ℝ)) * (y u .clet - x u .clet) := by
    intro u
    rw [og_sumT, og_sumT]
    simp only [price]
    simp
    ring
  have hload : ∑ u : Fin N, (σ - ρ) * (P.delta u / (P.n : ℝ)) * (y u .clet - x u .clet) =
      (σ - ρ) * (load P y - load P x) := by
    unfold load
    have e : (σ - ρ) * (1 / (P.n : ℝ) * ∑ v, P.delta v * y v OffloadGNEP.Exist.Tier.clet -
        1 / (P.n : ℝ) * ∑ v, P.delta v * x v OffloadGNEP.Exist.Tier.clet) =
        (σ - ρ) * (1 / (P.n : ℝ) * (∑ v, P.delta v * y v OffloadGNEP.Exist.Tier.clet -
        ∑ v, P.delta v * x v OffloadGNEP.Exist.Tier.clet)) := by ring
    rw [e, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  unfold pairE OffloadGNEP.Exist.pair Fe
  simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, Pi.add_apply]
  rw [Finset.sum_congr rfl (fun u _ => hu u), Finset.sum_add_distrib, hload]
  ring
