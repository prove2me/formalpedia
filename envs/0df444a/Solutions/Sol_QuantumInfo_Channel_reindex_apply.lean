-- Prove2me | solution 1 for QuantumInfo.Channel.reindex_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:49:20.731818+00:00
-- url     : https://prove2.me/submissions/f910c971-9adb-45a7-9770-255198cb4ded

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Definitions.Def_KnillLaflammeLean_Basic

set_option autoImplicit false
@[expose] public section
public section
open Matrix
open QuantumInfo
open QuantumInfo.Channel
variable {n m ι κ : Type*} [Fintype n] [Fintype m] [Fintype ι] [Fintype κ] [DecidableEq n]
namespace QuantumInfo.Channel
theorem _root_.solution (e : ι ≃ κ) (Φ : Channel n m ι) (ρ : Matrix n n ℂ) :
    (Φ.reindex e).apply ρ = Φ.apply ρ :=
  Equiv.sum_comp e.symm fun i => Φ.kraus i * ρ * (Φ.kraus i)ᴴ
end QuantumInfo.Channel
