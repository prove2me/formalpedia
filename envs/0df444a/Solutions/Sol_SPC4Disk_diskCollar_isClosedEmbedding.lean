-- Prove2me | solution 1 for SPC4Disk.diskCollar_isClosedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T05:59:00.671296+00:00
-- url     : https://prove2.me/submissions/f143a878-579f-444c-9e6a-d368e5b61f31

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_SPC4DiskCharts
import Definitions.Def_SPC4DiskCollar

set_option autoImplicit false

namespace SPC4Disk.SupplementAux_diskCollar_isClosedEmbedding

open Set Metric

open scoped ContDiff Manifold

noncomputable section

variable {n : ℕ} [NeZero n]

section BoundaryChart

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

end BoundaryChart

section BoundarySmooth

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

end BoundarySmooth

section Collar

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

lemma _root_.SPC4Disk.SupplementAux_diskCollar_isClosedEmbedding.continuous_diskCollar : Continuous (SPC4Disk.diskCollar (m := m)) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub ((continuous_subtype_val.comp
    continuous_snd).div_const 2)).smul
    (continuous_subtype_val.comp continuous_fst))

lemma _root_.SPC4Disk.SupplementAux_diskCollar_isClosedEmbedding.diskCollar_injective : Function.Injective (SPC4Disk.diskCollar (m := m)) := by
  rintro ⟨u, t⟩ ⟨v, s⟩ h
  have hval : (1 - t.val / 2) • u.val = (1 - s.val / 2) • v.val :=
    congrArg Subtype.val h
  have hnu : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have hnv : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hpt : (0 : ℝ) < 1 - t.val / 2 := by linarith [t.2.2]
  have hps : (0 : ℝ) < 1 - s.val / 2 := by linarith [s.2.2]
  have hn := congrArg norm hval
  rw [norm_smul, norm_smul, hnu, hnv, mul_one, mul_one, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hpt, abs_of_pos hps] at hn
  have hts : t = s := Subtype.ext (by linarith)
  subst hts
  have huv : u.val = v.val :=
    smul_right_injective _ (ne_of_gt hpt) hval
  exact Prod.ext (Subtype.ext huv) rfl

end Collar

section ValSmooth

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

end ValSmooth

section Annulus

variable {m : ℕ}

end Annulus

end
end SPC4Disk.SupplementAux_diskCollar_isClosedEmbedding

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

open SPC4Disk in
theorem solution :
    Topology.IsClosedEmbedding (SPC4Disk.diskCollar (m := m)) :=
  SPC4Disk.SupplementAux_diskCollar_isClosedEmbedding.continuous_diskCollar.isClosedEmbedding SPC4Disk.SupplementAux_diskCollar_isClosedEmbedding.diskCollar_injective
